import FormalConjectures.ErdosProblems.«399»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

-- Problem: Erdős Problem 399 — sum two squares
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/399.lean (declaration Erdos399.erdos_399.variants.sum_two_squares)
-- Credit: @caa1982 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Erdos399Proof

open Finset Real ArithmeticFunction Chebyshev

/- Step 1: Fermat sum-of-two-squares obstruction and factorial prime valuation -/

lemma not_sq_add_sq_of_prime_mod_four_eq_three {p n x y : ℕ}
    (hp : p.Prime) (hp3 : p % 4 = 3) (hdvd : p ∣ n) (hndvd : ¬ p ^ 2 ∣ n) :
    n ≠ x ^ 2 + y ^ 2 := by
  intro heq
  haveI : Fact p.Prime := ⟨hp⟩
  have hzero : ((x : ZMod p) ^ 2 + (y : ZMod p) ^ 2) = 0 := by
    have h1 : ((x ^ 2 + y ^ 2 : ℕ) : ZMod p) = 0 := by
      rw [← heq, ZMod.natCast_eq_zero_iff]
      exact hdvd
    simpa [Nat.cast_add, Nat.cast_pow] using h1
  have hpx : p ∣ x := by
    by_contra hnx
    have hx0 : (x : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff]
    have hsq : ((y : ZMod p) / (x : ZMod p)) ^ 2 = -1 := by
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hx0)]
      have : (y : ZMod p) ^ 2 = -(x : ZMod p) ^ 2 := eq_neg_of_add_eq_zero_right hzero
      rw [this]
      ring
    have hne3 : p % 4 ≠ 3 :=
      (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp ⟨(y : ZMod p) / (x : ZMod p), by rw [← sq, hsq]⟩
    exact hne3 hp3
  have hpy : p ∣ y := by
    have h1 : p ∣ y ^ 2 := by
      have hx2 : p ∣ x ^ 2 := dvd_pow hpx (by norm_num)
      rw [heq] at hdvd
      exact (Nat.dvd_add_right hx2).mp hdvd
    exact hp.dvd_of_dvd_pow h1
  rcases hpx with ⟨a, rfl⟩
  rcases hpy with ⟨b, rfl⟩
  apply hndvd
  refine ⟨a ^ 2 + b ^ 2, ?_⟩
  rw [heq]
  ring

lemma not_sq_dvd_factorial_of_lt_two_mul {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n) (hn2p : n < 2 * p) :
    ¬ p ^ 2 ∣ n.factorial := by
  have hval : padicValNat p n.factorial = 1 := by
    haveI : Fact p.Prime := ⟨hp⟩
    rw [padicValNat_factorial (b := 2)]
    · rw [show Finset.Ico 1 2 = {1} by decide, Finset.sum_singleton, pow_one]
      have h1 : 1 ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).mpr (by omega)
      have h2 : n / p < 2 := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega)
      omega
    · apply Nat.log_lt_of_lt_pow (by omega)
      have hp2 : 2 ≤ p := hp.two_le
      have hsq : p ^ 2 = p * p := sq p
      nlinarith
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have h2 : 2 ≤ padicValNat p n.factorial :=
    (padicValNat_dvd_iff_le hne).mp hdvd
  omega

lemma not_factorial_eq_sq_add_sq_of_prime_in_interval {n p x y : ℕ}
    (hp : p.Prime) (hp3 : p % 4 = 3) (hlo : n / 2 < p) (hhi : p ≤ n) :
    n.factorial ≠ x ^ 2 + y ^ 2 := by
  apply not_sq_add_sq_of_prime_mod_four_eq_three hp hp3
  · exact hp.dvd_factorial.mpr hhi
  · exact not_sq_dvd_factorial_of_lt_two_mul hp hhi (by omega)

/- Step 2: Elementary log bounds and Stirling for log(n!) -/

lemma log_two_bounds : (0.6931 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.6932 := by
  constructor
  · linarith [Real.log_two_gt_d9]
  · linarith [Real.log_two_lt_d9]

lemma log_three_bounds : (1.097 : ℝ) < Real.log 3 ∧ Real.log 3 < 1.101 := by
  have ⟨h2lo, h2hi⟩ := log_two_bounds
  constructor
  · have hpow : (2 : ℝ) ^ (19 : ℕ) < (3 : ℝ) ^ (12 : ℕ) := by norm_num
    have hlog := Real.log_lt_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow] at hlog
    push_cast at hlog
    linarith
  · have hpow : (3 : ℝ) ^ (17 : ℕ) < (2 : ℝ) ^ (27 : ℕ) := by norm_num
    have hlog := Real.log_lt_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow] at hlog
    push_cast at hlog
    linarith

lemma log_five_bounds : (1.602 : ℝ) < Real.log 5 ∧ Real.log 5 < 1.618 := by
  have ⟨h2lo, h2hi⟩ := log_two_bounds
  constructor
  · have hpow : (2 : ℝ) ^ (37 : ℕ) < (5 : ℝ) ^ (16 : ℕ) := by norm_num
    have hlog := Real.log_lt_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow] at hlog
    push_cast at hlog
    linarith
  · have hpow : (5 : ℝ) ^ (3 : ℕ) < (2 : ℝ) ^ (7 : ℕ) := by norm_num
    have hlog := Real.log_lt_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow] at hlog
    push_cast at hlog
    linarith

noncomputable def logFact (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, Real.log k

lemma logFact_zero : logFact 0 = 0 := by simp [logFact]

lemma logFact_succ (n : ℕ) : logFact (n + 1) = logFact n + Real.log (n + 1 : ℕ) := by
  simp only [logFact]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

lemma stirling_lo (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n + 1 ≤ logFact n := by
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      simp [logFact]
    | succ k =>
      have hk1 : 1 ≤ k + 1 := by omega
      have hih := ih hk1
      rw [logFact_succ]
      have hk_pos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      have hk2_pos : (0 : ℝ) < (k + 2 : ℕ) := by positivity
      have hlog_step : ((k + 1 : ℕ) : ℝ) * Real.log ((k + 2 : ℕ) : ℝ) -
          ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) ≤ 1 := by
        have h1 : Real.log (((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) ≤
            ((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_div (ne_of_gt hk2_pos) (ne_of_gt hk_pos)] at h1
        have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hk_pos)
        have h3 : ((k + 1 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) - 1) = 1 := by
          field_simp
          push_cast
          ring
        linarith
      push_cast at hlog_step hih ⊢
      rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring]
      linarith

lemma stirling_hi (n : ℕ) (hn : 1 ≤ n) :
    logFact n ≤ (n : ℝ) * Real.log n - n + Real.log n + 1 := by
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      simp [logFact]
    | succ k =>
      have hk1 : 1 ≤ k + 1 := by omega
      have hih := ih hk1
      rw [logFact_succ]
      have hk_pos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      have hk2_pos : (0 : ℝ) < (k + 2 : ℕ) := by positivity
      have hlog_step : 1 ≤ ((k + 2 : ℕ) : ℝ) * Real.log ((k + 2 : ℕ) : ℝ) -
          ((k + 2 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) := by
        have h1 : Real.log (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ≤
            ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_div (ne_of_gt hk_pos) (ne_of_gt hk2_pos)] at h1
        have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hk2_pos)
        have h3 : ((k + 2 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) - 1) = -1 := by
          field_simp
          push_cast
          ring
        linarith
      push_cast at hlog_step hih ⊢
      rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring]
      linarith

lemma logFact_eq_sum_vonMangoldt (n : ℕ) :
    logFact n = ∑ d ∈ Finset.Icc 1 n, Λ d * ((n / d : ℕ) : ℝ) := by
  simp only [logFact]
  have h1 : ∀ k ∈ Finset.Icc 1 n, Real.log (k : ℝ) = ∑ d ∈ k.divisors, Λ d := fun k _ =>
    (ArithmeticFunction.vonMangoldt_sum (n := k)).symm
  rw [Finset.sum_congr rfl h1]
  have hswap :
      (∑ k ∈ Finset.Icc 1 n, ∑ d ∈ k.divisors, Λ d) =
      ∑ d ∈ Finset.Icc 1 n, ∑ k ∈ (Finset.Icc 1 n).filter (fun k => d ∣ k), Λ d := by
    have hinner : ∀ k ∈ Finset.Icc 1 n,
        (∑ d ∈ k.divisors, Λ d) = ∑ d ∈ Finset.Icc 1 n, if d ∣ k then Λ d else 0 := by
      intro k hk
      have hk_pos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk_le : k ≤ n := (Finset.mem_Icc.mp hk).2
      rw [← Finset.sum_filter]
      congr 1
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hd, hk0⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd hk_pos, (Nat.le_of_dvd hk_pos hd).trans hk_le⟩, hd⟩
      · rintro ⟨_, hd⟩
        exact ⟨hd, by omega⟩
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_filter]
  rw [hswap]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd_pos : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have hcard : ((Finset.Icc 1 n).filter (fun k => d ∣ k)).card = n / d := by
    have hbij : (Finset.Icc 1 n).filter (fun k => d ∣ k) =
        (Finset.Icc 1 (n / d)).image (fun q => d * q) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hk1, hkn⟩, ⟨q, rfl⟩⟩
        refine ⟨q, ⟨?_, ?_⟩, rfl⟩
        · by_contra hq0
          have : q = 0 := by omega
          subst this; simp at hk1
        · exact (Nat.le_div_iff_mul_le hd_pos).mpr (by linarith)
      · rintro ⟨q, ⟨hq1, hqn⟩, rfl⟩
        refine ⟨⟨?_, ?_⟩, ⟨q, rfl⟩⟩
        · nlinarith
        · have := (Nat.le_div_iff_mul_le hd_pos).mp hqn
          linarith
    rw [hbij, Finset.card_image_of_injective _ (mul_right_injective₀ (by omega : d ≠ 0)),
      Nat.card_Icc]
    simp
  exact_mod_cast hcard

/- Step 3: Chebyshev 30-trick for tight ψ(n) bounds -/

def g30 (u : ℕ) : ℤ :=
  (u : ℤ) - (u / 2 : ℕ) - (u / 3 : ℕ) - (u / 5 : ℕ) + (u / 30 : ℕ)

lemma g30_period (u : ℕ) : g30 (u + 30) = g30 u := by
  simp only [g30]
  omega

lemma g30_bounds (u : ℕ) : 0 ≤ g30 u ∧ g30 u ≤ 1 := by
  have hred : g30 u = g30 (u % 30) := by
    have hdiv : u = u % 30 + 30 * (u / 30) := (Nat.mod_add_div u 30).symm
    have hstep : ∀ q, g30 (u % 30 + 30 * q) = g30 (u % 30) := by
      intro q
      induction q with
      | zero => simp
      | succ q ih =>
        rw [show u % 30 + 30 * (q + 1) = (u % 30 + 30 * q) + 30 by ring, g30_period, ih]
    conv_lhs => rw [hdiv, hstep]
  rw [hred]
  have hlt : u % 30 < 30 := Nat.mod_lt u (by norm_num)
  have hdec : ∀ r : Fin 30, 0 ≤ g30 r.val ∧ g30 r.val ≤ 1 := by decide
  exact hdec ⟨u % 30, hlt⟩

lemma g30_eq_one_of_lt_six {u : ℕ} (h1 : 1 ≤ u) (h6 : u < 6) : g30 u = 1 := by
  simp only [g30]
  omega

noncomputable def A30 (n : ℕ) : ℝ :=
  logFact n - logFact (n / 2) - logFact (n / 3) - logFact (n / 5) + logFact (n / 30)

lemma psi_eq_sum_Icc (n : ℕ) : ψ (n : ℝ) = ∑ d ∈ Finset.Icc 1 n, Λ d := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have hsplit : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
    ext d; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  simp

lemma A30_eq_sum_g30 (n : ℕ) :
    A30 n = ∑ d ∈ Finset.Icc 1 n, Λ d * (g30 (n / d) : ℝ) := by
  simp only [A30, logFact_eq_sum_vonMangoldt]
  have hext : ∀ k : ℕ, 1 ≤ k →
      (∑ d ∈ Finset.Icc 1 (n / k), Λ d * ((n / k / d : ℕ) : ℝ)) =
      ∑ d ∈ Finset.Icc 1 n, Λ d * ((n / d / k : ℕ) : ℝ) := by
    intro k hk
    have hsub : Finset.Icc 1 (n / k) ⊆ Finset.Icc 1 n :=
      Finset.Icc_subset_Icc_right (Nat.div_le_self n k)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun d _ => ?_
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm k d]
    · intro d hd hnd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hgt : n / k < d := by
        simp only [Finset.mem_Icc] at hnd
        omega
      have hzero : n / d / k = 0 := by
        rw [Nat.div_div_eq_div_mul, mul_comm d k, ← Nat.div_div_eq_div_mul]
        exact Nat.div_eq_of_lt hgt
      simp [hzero]
  rw [hext 2 (by norm_num), hext 3 (by norm_num), hext 5 (by norm_num), hext 30 (by norm_num)]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [g30, Int.cast_add, Int.cast_sub, Int.cast_natCast]
  ring

lemma A30_le_psi (n : ℕ) : A30 n ≤ ψ (n : ℝ) := by
  rw [A30_eq_sum_g30, psi_eq_sum_Icc]
  refine Finset.sum_le_sum fun d _ => ?_
  have hL : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
  have hg : (g30 (n / d) : ℝ) ≤ 1 := by exact_mod_cast (g30_bounds (n / d)).2
  nlinarith

lemma psi_sub_psi_div_six_le_A30 (n : ℕ) :
    ψ (n : ℝ) - ψ ((n / 6 : ℕ) : ℝ) ≤ A30 n := by
  rw [A30_eq_sum_g30, psi_eq_sum_Icc, psi_eq_sum_Icc]
  have hsub : Finset.Icc 1 (n / 6) ⊆ Finset.Icc 1 n :=
    Finset.Icc_subset_Icc_right (Nat.div_le_self n 6)
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  calc ∑ d ∈ Finset.Icc 1 n \ Finset.Icc 1 (n / 6), Λ d
      = ∑ d ∈ Finset.Icc 1 n \ Finset.Icc 1 (n / 6), Λ d * (g30 (n / d) : ℝ) := by
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd1 : 1 ≤ d ∧ d ≤ n := Finset.mem_Icc.mp (Finset.mem_sdiff.mp hd).1
        have hgt : n / 6 < d := by
          have hnot := (Finset.mem_sdiff.mp hd).2
          simp only [Finset.mem_Icc] at hnot
          omega
        have h1 : 1 ≤ n / d := (Nat.le_div_iff_mul_le hd1.1).mpr (by omega)
        have h6 : n / d < 6 := (Nat.div_lt_iff_lt_mul hd1.1).mpr (by
          have : n < 6 * (n / 6 + 1) := by omega
          nlinarith)
        rw [g30_eq_one_of_lt_six h1 h6]
        simp
    _ ≤ ∑ d ∈ Finset.Icc 1 n, Λ d * (g30 (n / d) : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun d _ _ => ?_
        have hL : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
        have hg : (0 : ℝ) ≤ (g30 (n / d) : ℝ) := by exact_mod_cast (g30_bounds (n / d)).1
        exact mul_nonneg hL hg

lemma xlogx_sub_div_bound {n k : ℕ} (hk : 1 ≤ k) (hnk : k ≤ n) :
    let m := n / k
    ((n : ℝ) / k) * Real.log ((n : ℝ) / k) - (n : ℝ) / k - Real.log n ≤
      (m : ℝ) * Real.log m - m ∧
    (m : ℝ) * Real.log m - m ≤
      ((n : ℝ) / k) * Real.log ((n : ℝ) / k) - (n : ℝ) / k := by
  intro m
  have hm_pos : 1 ≤ m := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr (by omega)
  have hm_r : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
  have hm_pos_r : (0 : ℝ) < (m : ℝ) := by linarith
  have hk_r : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hn_pos_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hm_le : (m : ℝ) ≤ (n : ℝ) / k := by
    rw [le_div_iff₀ hk_r]
    exact_mod_cast Nat.div_mul_le_self n k
  have hm_gt : (n : ℝ) / k - 1 ≤ (m : ℝ) := by
    have hlt_nat : n < (m + 1) * k := by
      have h1 := Nat.div_add_mod n k
      have h2 := Nat.mod_lt n (by omega : 0 < k)
      have h3 : k * m + n % k = n := h1
      nlinarith
    have h1 : (n : ℝ) < ((m : ℝ) + 1) * k := by exact_mod_cast hlt_nat
    rw [sub_le_iff_le_add, div_le_iff₀ hk_r]
    linarith
  have hlog_mono : Real.log (m : ℝ) ≤ Real.log ((n : ℝ) / k) :=
    Real.log_le_log hm_pos_r hm_le
  have hlog_div_le : Real.log ((n : ℝ) / k) ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log (div_pos hn_pos_r hk_r)
    exact div_le_self (le_of_lt hn_pos_r) (by exact_mod_cast hk)
  have hlog_m_nonneg : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm_r
  have hlog_nk_nonneg : 0 ≤ Real.log ((n : ℝ) / k) := le_trans hlog_m_nonneg hlog_mono
  constructor
  · have h1 : ((n : ℝ) / k - (m : ℝ)) * Real.log ((n : ℝ) / k) ≤ Real.log (n : ℝ) := by
      have hdiff : (n : ℝ) / k - (m : ℝ) ≤ 1 := by linarith
      have hdiff0 : 0 ≤ (n : ℝ) / k - (m : ℝ) := by linarith
      calc ((n : ℝ) / k - (m : ℝ)) * Real.log ((n : ℝ) / k)
          ≤ 1 * Real.log ((n : ℝ) / k) := mul_le_mul_of_nonneg_right hdiff hlog_nk_nonneg
        _ = Real.log ((n : ℝ) / k) := one_mul _
        _ ≤ Real.log (n : ℝ) := hlog_div_le
    have h2 : (m : ℝ) * (Real.log ((n : ℝ) / k) - Real.log (m : ℝ)) ≤ (n : ℝ) / k - (m : ℝ) := by
      have h3 := Real.log_le_sub_one_of_pos (div_pos (div_pos hn_pos_r hk_r) hm_pos_r)
      rw [Real.log_div (ne_of_gt (div_pos hn_pos_r hk_r)) (ne_of_gt hm_pos_r)] at h3
      have h4 := mul_le_mul_of_nonneg_left h3 (le_of_lt hm_pos_r)
      have h5 : (m : ℝ) * (((n : ℝ) / k) / (m : ℝ) - 1) = (n : ℝ) / k - (m : ℝ) := by
        field_simp
      linarith
    linarith
  · have h3 := Real.log_le_sub_one_of_pos (div_pos hm_pos_r (div_pos hn_pos_r hk_r))
    rw [Real.log_div (ne_of_gt hm_pos_r) (ne_of_gt (div_pos hn_pos_r hk_r))] at h3
    have h4 := mul_le_mul_of_nonneg_left h3 (le_of_lt (div_pos hn_pos_r hk_r))
    have h5 : ((n : ℝ) / k) * ((m : ℝ) / ((n : ℝ) / k) - 1) = (m : ℝ) - (n : ℝ) / k := by
      field_simp
    have h6 : ((n : ℝ) / k - (m : ℝ)) * Real.log (m : ℝ) ≥ 0 :=
      mul_nonneg (by linarith) hlog_m_nonneg
    nlinarith

lemma A30_bounds (n : ℕ) (hn : 30 ≤ n) :
    (0.919 : ℝ) * n - 6 * Real.log n - 5 ≤ A30 n ∧
    A30 n ≤ (0.924 : ℝ) * n + 6 * Real.log n + 5 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hst_n := And.intro (stirling_lo n (by omega)) (stirling_hi n (by omega))
  have hst_2 := And.intro (stirling_lo (n / 2) (by omega)) (stirling_hi (n / 2) (by omega))
  have hst_3 := And.intro (stirling_lo (n / 3) (by omega)) (stirling_hi (n / 3) (by omega))
  have hst_5 := And.intro (stirling_lo (n / 5) (by omega)) (stirling_hi (n / 5) (by omega))
  have hst_30 := And.intro (stirling_lo (n / 30) (by omega)) (stirling_hi (n / 30) (by omega))
  have hx2 := xlogx_sub_div_bound (n := n) (k := 2) (by norm_num) (by omega)
  have hx3 := xlogx_sub_div_bound (n := n) (k := 3) (by norm_num) (by omega)
  have hx5 := xlogx_sub_div_bound (n := n) (k := 5) (by norm_num) (by omega)
  have hx30 := xlogx_sub_div_bound (n := n) (k := 30) (by norm_num) (by omega)
  have hlog_le : ∀ k : ℕ, 1 ≤ k → k ≤ n → Real.log ((n / k : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
    intro k hk hkn
    apply Real.log_le_log
    · have : 1 ≤ n / k := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr (by omega)
      exact_mod_cast this
    · exact_mod_cast Nat.div_le_self n k
  have hlog2_le := hlog_le 2 (by norm_num) (by omega)
  have hlog3_le := hlog_le 3 (by norm_num) (by omega)
  have hlog5_le := hlog_le 5 (by norm_num) (by omega)
  have hlog30_le := hlog_le 30 (by norm_num) (by omega)
  have hlog30_eq : Real.log (30 : ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  have hcomb :
      ((n : ℝ) * Real.log n - n) -
      (((n : ℝ) / 2) * Real.log ((n : ℝ) / 2) - (n : ℝ) / 2) -
      (((n : ℝ) / 3) * Real.log ((n : ℝ) / 3) - (n : ℝ) / 3) -
      (((n : ℝ) / 5) * Real.log ((n : ℝ) / 5) - (n : ℝ) / 5) +
      (((n : ℝ) / 30) * Real.log ((n : ℝ) / 30) - (n : ℝ) / 30) =
      ((14 / 30 : ℝ) * Real.log 2 + (9 / 30 : ℝ) * Real.log 3 + (5 / 30 : ℝ) * Real.log 5) * n := by
    rw [Real.log_div (ne_of_gt hn_pos) (by norm_num),
      Real.log_div (ne_of_gt hn_pos) (by norm_num),
      Real.log_div (ne_of_gt hn_pos) (by norm_num),
      Real.log_div (ne_of_gt hn_pos) (by norm_num), hlog30_eq]
    ring
  have ⟨h2lo, h2hi⟩ := log_two_bounds
  have ⟨h3lo, h3hi⟩ := log_three_bounds
  have ⟨h5lo, h5hi⟩ := log_five_bounds
  have hc_lo : (0.919 : ℝ) ≤ (14 / 30 : ℝ) * Real.log 2 + (9 / 30 : ℝ) * Real.log 3 +
      (5 / 30 : ℝ) * Real.log 5 := by linarith
  have hc_hi : (14 / 30 : ℝ) * Real.log 2 + (9 / 30 : ℝ) * Real.log 3 +
      (5 / 30 : ℝ) * Real.log 5 ≤ (0.924 : ℝ) := by linarith
  simp only [A30]
  constructor
  · have hmul : (0.919 : ℝ) * n ≤
        ((14 / 30 : ℝ) * Real.log 2 + (9 / 30 : ℝ) * Real.log 3 +
          (5 / 30 : ℝ) * Real.log 5) * n :=
      mul_le_mul_of_nonneg_right hc_lo (le_of_lt hn_pos)
    linarith [hst_n.1, hst_2.2, hst_3.2, hst_5.2, hst_30.1,
      hx2.2, hx3.2, hx5.2, hx30.1, hlog2_le, hlog3_le, hlog5_le, hcomb]
  · have hmul :
        ((14 / 30 : ℝ) * Real.log 2 + (9 / 30 : ℝ) * Real.log 3 +
          (5 / 30 : ℝ) * Real.log 5) * n ≤ (0.924 : ℝ) * n :=
      mul_le_mul_of_nonneg_right hc_hi (le_of_lt hn_pos)
    linarith [hst_n.2, hst_2.1, hst_3.1, hst_5.1, hst_30.2,
      hx2.1, hx3.1, hx5.1, hx30.2, hlog30_le, hcomb]

lemma psi_ge_tight (n : ℕ) (hn : 30 ≤ n) :
    (0.919 : ℝ) * n - 6 * Real.log n - 5 ≤ ψ (n : ℝ) :=
  le_trans (A30_bounds n hn).1 (A30_le_psi n)

lemma psi_le_tight (n : ℕ) (hn : 1 ≤ n) :
    ψ (n : ℝ) ≤ (1.1088 : ℝ) * n + 10 * (Real.log n) ^ 2 + 60 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h30 : n < 30
    · have h1 : ψ (n : ℝ) ≤ Real.log 4 * n + 2 * Real.sqrt n * Real.log n :=
        Chebyshev.psi_le (by exact_mod_cast hn)
      have hlog4 : Real.log (4 : ℝ) < 1.4 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
        push_cast
        linarith [log_two_bounds.2]
      have hlogn : Real.log (n : ℝ) ≤ 4 := by
        have hlt : (n : ℝ) ≤ (2 : ℝ) ^ (5 : ℕ) := by exact_mod_cast (by omega : n ≤ 32)
        have h2 := Real.log_le_log (by positivity) hlt
        rw [Real.log_pow] at h2
        push_cast at h2
        linarith [log_two_bounds.2]
      have hsq : Real.sqrt (n : ℝ) ≤ 6 := by
        rw [Real.sqrt_le_left (by norm_num)]
        exact_mod_cast (by omega : n ≤ 36)
      have hn_le : (n : ℝ) ≤ 30 := by exact_mod_cast (by omega : n ≤ 30)
      have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
      nlinarith
    · have hn30 : 30 ≤ n := by omega
      have hdiv_lt : n / 6 < n := Nat.div_lt_self (by omega) (by norm_num)
      have hdiv_pos : 1 ≤ n / 6 := by omega
      have hih := ih (n / 6) hdiv_lt hdiv_pos
      have hA := psi_sub_psi_div_six_le_A30 n
      have hA_hi := (A30_bounds n hn30).2
      have hdiv_le : ((n / 6 : ℕ) : ℝ) ≤ (n : ℝ) / 6 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
        exact_mod_cast Nat.div_mul_le_self n 6
      have hlog6_gt : (1.79 : ℝ) < Real.log 6 := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        linarith [log_two_bounds.1, log_three_bounds.1]
      have hlog_div : Real.log ((n / 6 : ℕ) : ℝ) ≤ Real.log n - 1.79 := by
        have h1 : Real.log ((n / 6 : ℕ) : ℝ) ≤ Real.log ((n : ℝ) / 6) :=
          Real.log_le_log (by exact_mod_cast hdiv_pos) hdiv_le
        rw [Real.log_div (by positivity) (by norm_num)] at h1
        linarith
      have hlog_div_nonneg : 0 ≤ Real.log ((n / 6 : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hdiv_pos)
      have hlogn_ge : (3.39 : ℝ) ≤ Real.log n := by
        have h1 : Real.log (30 : ℝ) ≤ Real.log n :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hn30)
        rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
          Real.log_mul (by norm_num) (by norm_num)] at h1
        linarith [log_two_bounds.1, log_three_bounds.1, log_five_bounds.1]
      have hsq_le : (Real.log ((n / 6 : ℕ) : ℝ)) ^ 2 ≤ (Real.log n - 1.79) ^ 2 := by
        nlinarith
      nlinarith

/- Step 4: Character sum T(n) = ∑ χ₄(k) log k and W(u) isolation -/

def chi4 (n : ℕ) : ℤ :=
  if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

lemma chi4_mul (a b : ℕ) : chi4 (a * b) = chi4 a * chi4 b := by
  simp only [chi4]
  rw [Nat.mul_mod]
  have ha : a % 4 < 4 := Nat.mod_lt a (by norm_num)
  have hb : b % 4 < 4 := Nat.mod_lt b (by norm_num)
  interval_cases (a % 4) <;> interval_cases (b % 4) <;> decide

lemma chi4_abs_le_one (n : ℕ) : |(chi4 n : ℝ)| ≤ 1 := by
  simp only [chi4]
  split_ifs <;> norm_num

def H4 (n : ℕ) : ℤ := if n % 4 = 1 ∨ n % 4 = 2 then 1 else 0

lemma sum_chi4_Icc (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, chi4 k = H4 n := by
  induction n with
  | zero => simp [H4]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
    simp only [H4, chi4]
    omega

noncomputable def T4 (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, (chi4 k : ℝ) * Real.log k

lemma T4_abs_le_log (n : ℕ) (hn : 1 ≤ n) : |T4 n| ≤ Real.log n := by
  have hmain : ∀ m : ℕ, 1 ≤ m →
      (m % 4 = 0 → -Real.log m ≤ T4 m ∧ T4 m ≤ 0) ∧
      (m % 4 = 1 → 0 ≤ T4 m ∧ T4 m ≤ Real.log m) ∧
      (m % 4 = 2 → 0 ≤ T4 m ∧ T4 m ≤ Real.log m) ∧
      (m % 4 = 3 → -Real.log m ≤ T4 m ∧ T4 m ≤ 0) := by
    intro m hm
    induction m with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero =>
        simp [T4, chi4]
      | succ j =>
        have hk1 : 1 ≤ j + 1 := by omega
        have hih := ih hk1
        have hstep : T4 (j + 2) = T4 (j + 1) + (chi4 (j + 2) : ℝ) * Real.log (j + 2 : ℕ) := by
          simp only [T4]
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 2)]
        have hlog_mono : Real.log ((j + 1 : ℕ) : ℝ) ≤ Real.log ((j + 2 : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast (by omega : j + 1 ≤ j + 2))
        have hlog_nn : 0 ≤ Real.log ((j + 2 : ℕ) : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ j + 2))
        have hcast2 : ((j + 1 + 1 : ℕ) : ℝ) = ((j + 2 : ℕ) : ℝ) := by norm_cast
        refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
        · have hprev : (j + 1) % 4 = 3 := by omega
          have ⟨hlo, hhi⟩ := hih.2.2.2 hprev
          have hchi : chi4 (j + 2) = 0 := by simp [chi4]; omega
          rw [hcast2, hstep, hchi]; simp only [Int.cast_zero, zero_mul, add_zero]; constructor <;> linarith
        · have hprev : (j + 1) % 4 = 0 := by omega
          have ⟨hlo, hhi⟩ := hih.1 hprev
          have hchi : chi4 (j + 2) = 1 := by simp [chi4]; omega
          rw [hcast2, hstep, hchi]; simp only [Int.cast_one, one_mul]; constructor <;> linarith
        · have hprev : (j + 1) % 4 = 1 := by omega
          have ⟨hlo, hhi⟩ := hih.2.1 hprev
          have hchi : chi4 (j + 2) = 0 := by simp [chi4]; omega
          rw [hcast2, hstep, hchi]; simp only [Int.cast_zero, zero_mul, add_zero]; constructor <;> linarith
        · have hprev : (j + 1) % 4 = 2 := by omega
          have ⟨hlo, hhi⟩ := hih.2.2.1 hprev
          have hchi : chi4 (j + 2) = -1 := by simp [chi4]; omega
          rw [hcast2, hstep, hchi]; simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul]; constructor <;> linarith
  have h := hmain n hn
  have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hmod with h0 | h1 | h2 | h3
  · have ⟨a, b⟩ := h.1 h0; rw [abs_le]; constructor <;> linarith
  · have ⟨a, b⟩ := h.2.1 h1; rw [abs_le]; constructor <;> linarith [Real.log_nonneg (by exact_mod_cast hn : (1 : ℝ) ≤ n)]
  · have ⟨a, b⟩ := h.2.2.1 h2; rw [abs_le]; constructor <;> linarith [Real.log_nonneg (by exact_mod_cast hn : (1 : ℝ) ≤ n)]
  · have ⟨a, b⟩ := h.2.2.2 h3; rw [abs_le]; constructor <;> linarith

lemma T4_eq_sum_vonMangoldt (n : ℕ) :
    T4 n = ∑ d ∈ Finset.Icc 1 n, (chi4 d : ℝ) * Λ d * (H4 (n / d) : ℝ) := by
  simp only [T4]
  have h1 : ∀ k ∈ Finset.Icc 1 n, (chi4 k : ℝ) * Real.log (k : ℝ) =
      ∑ d ∈ k.divisors, (chi4 k : ℝ) * Λ d := by
    intro k _
    rw [← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum]
  rw [Finset.sum_congr rfl h1]
  have hswap :
      (∑ k ∈ Finset.Icc 1 n, ∑ d ∈ k.divisors, (chi4 k : ℝ) * Λ d) =
      ∑ d ∈ Finset.Icc 1 n, ∑ k ∈ (Finset.Icc 1 n).filter (fun k => d ∣ k), (chi4 k : ℝ) * Λ d := by
    have hinner : ∀ k ∈ Finset.Icc 1 n,
        (∑ d ∈ k.divisors, (chi4 k : ℝ) * Λ d) =
        ∑ d ∈ Finset.Icc 1 n, if d ∣ k then (chi4 k : ℝ) * Λ d else 0 := by
      intro k hk
      have hk_pos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk_le : k ≤ n := (Finset.mem_Icc.mp hk).2
      rw [← Finset.sum_filter]
      congr 1
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd hk_pos, (Nat.le_of_dvd hk_pos hd).trans hk_le⟩, hd⟩
      · rintro ⟨_, hd⟩
        exact ⟨hd, by omega⟩
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_filter]
  rw [hswap]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd_pos : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hbij : (Finset.Icc 1 n).filter (fun k => d ∣ k) =
      (Finset.Icc 1 (n / d)).image (fun q => d * q) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hk1, hkn⟩, ⟨q, rfl⟩⟩
      refine ⟨q, ⟨?_, ?_⟩, rfl⟩
      · by_contra hq0; have hq : q = 0 := by omega
        rw [hq, mul_zero] at hk1; omega
      · exact (Nat.le_div_iff_mul_le hd_pos).mpr (by linarith)
    · rintro ⟨q, ⟨hq1, hqn⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨q, rfl⟩⟩
      · nlinarith
      · have := (Nat.le_div_iff_mul_le hd_pos).mp hqn; linarith
  rw [hbij, Finset.sum_image (fun a _ b _ h => mul_right_injective₀ (by omega : d ≠ 0) h)]
  have hmul : ∀ q ∈ Finset.Icc 1 (n / d),
      (chi4 (d * q) : ℝ) * Λ d = (chi4 d : ℝ) * Λ d * (chi4 q : ℝ) := by
    intro q _
    rw [chi4_mul, Int.cast_mul]
    ring
  rw [Finset.sum_congr rfl hmul, ← Finset.mul_sum]
  congr 1
  have := sum_chi4_Icc (n / d)
  exact_mod_cast this

def W4 (u : ℕ) : ℤ := H4 u - H4 (u / 2) + H4 (u / 3) - H4 (u / 6)

lemma W4_values (u : ℕ) :
    (u = 1 → W4 u = 1) ∧
    (2 ≤ u ∧ u ≤ 4 → W4 u = 0) ∧
    (5 ≤ u ∧ u ≤ 6 → W4 u = 1) ∧
    (7 ≤ u ∧ u ≤ 9 → W4 u = 0) ∧
    |W4 u| ≤ 2 := by
  simp only [W4, H4]
  refine ⟨fun h => by subst h; decide, fun ⟨h1, h2⟩ => by interval_cases u <;> decide,
    fun ⟨h1, h2⟩ => by interval_cases u <;> decide,
    fun ⟨h1, h2⟩ => by interval_cases u <;> decide, ?_⟩
  split_ifs <;> norm_num

lemma chi4_half_interval_bound (n : ℕ) (hn : 10 ≤ n) :
    ∑ d ∈ Finset.Icc (n / 2 + 1) n, (chi4 d : ℝ) * Λ d ≤
      4 * Real.log n + (ψ ((n / 5 : ℕ) : ℝ) - ψ ((n / 7 : ℕ) : ℝ)) +
        2 * ψ ((n / 10 : ℕ) : ℝ) := by
  have hext : ∀ k : ℕ, 1 ≤ k →
      T4 (n / k) = ∑ d ∈ Finset.Icc 1 n, (chi4 d : ℝ) * Λ d * (H4 (n / d / k) : ℝ) := by
    intro k hk
    rw [T4_eq_sum_vonMangoldt]
    have hsub : Finset.Icc 1 (n / k) ⊆ Finset.Icc 1 n :=
      Finset.Icc_subset_Icc_right (Nat.div_le_self n k)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun d _ => ?_
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm k d]
    · intro d hd hnd
      have hgt : n / k < d := by simp only [Finset.mem_Icc] at hd hnd; omega
      have hzero : n / d / k = 0 := by
        rw [Nat.div_div_eq_div_mul, mul_comm d k, ← Nat.div_div_eq_div_mul]
        exact Nat.div_eq_of_lt hgt
      simp [hzero, H4]
  have hcomb : T4 n - T4 (n / 2) + T4 (n / 3) - T4 (n / 6) =
      ∑ d ∈ Finset.Icc 1 n, (chi4 d : ℝ) * Λ d * (W4 (n / d) : ℝ) := by
    rw [T4_eq_sum_vonMangoldt, hext 2 (by norm_num), hext 3 (by norm_num), hext 6 (by norm_num)]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [W4, Int.cast_add, Int.cast_sub]
    ring
  have hT_le : T4 n - T4 (n / 2) + T4 (n / 3) - T4 (n / 6) ≤ 4 * Real.log n := by
    have hlog_div : ∀ k : ℕ, 1 ≤ k → k ≤ n → |T4 (n / k)| ≤ Real.log n := by
      intro k hk hkn
      have h1 : 1 ≤ n / k := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr (by omega)
      calc |T4 (n / k)| ≤ Real.log ((n / k : ℕ) : ℝ) := T4_abs_le_log (n / k) h1
        _ ≤ Real.log n := Real.log_le_log (by exact_mod_cast h1) (by exact_mod_cast Nat.div_le_self n k)
    have h1 := T4_abs_le_log n (by omega)
    have h2 := hlog_div 2 (by norm_num) (by omega)
    have h3 := hlog_div 3 (by norm_num) (by omega)
    have h6 := hlog_div 6 (by norm_num) (by omega)
    linarith [(abs_le.mp h1).2, (abs_le.mp h2).1, (abs_le.mp h3).2, (abs_le.mp h6).1]
  -- Split Icc 1 n into (n/2, n] and [1, n/2]
  have hsplit :
      (∑ d ∈ Finset.Icc 1 n, (chi4 d : ℝ) * Λ d * (W4 (n / d) : ℝ)) =
      (∑ d ∈ Finset.Icc (n / 2 + 1) n, (chi4 d : ℝ) * Λ d) +
      (∑ d ∈ Finset.Icc 1 (n / 2), (chi4 d : ℝ) * Λ d * (W4 (n / d) : ℝ)) := by
    have hunion : Finset.Icc 1 n = Finset.Icc 1 (n / 2) ∪ Finset.Icc (n / 2 + 1) n := by
      ext d; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 1 (n / 2)) (Finset.Icc (n / 2 + 1) n) := by
      rw [Finset.disjoint_left]; intro d h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    rw [hunion, Finset.sum_union hdisj, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd' := Finset.mem_Icc.mp hd
    have hq : n / d = 1 := by
      have h1 : 1 ≤ n / d := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr (by omega)
      have h2 : n / d < 2 := (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).mpr (by omega)
      omega
    rw [(W4_values (n / d)).1 hq]
    simp
  -- Bound the tail sum for d ∈ [1, n/2]
  have htail :
      -(∑ d ∈ Finset.Icc 1 (n / 2), (chi4 d : ℝ) * Λ d * (W4 (n / d) : ℝ)) ≤
      (ψ ((n / 5 : ℕ) : ℝ) - ψ ((n / 7 : ℕ) : ℝ)) + 2 * ψ ((n / 10 : ℕ) : ℝ) := by
    have hbound_term : ∀ d ∈ Finset.Icc 1 (n / 2),
        -((chi4 d : ℝ) * Λ d * (W4 (n / d) : ℝ)) ≤
        (if d ∈ Finset.Icc (n / 7 + 1) (n / 5) then Λ d else 0) +
        (if d ∈ Finset.Icc 1 (n / 10) then 2 * Λ d else 0) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hd2 : d ≤ n / 2 := (Finset.mem_Icc.mp hd).2
      have hL : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
      have hchi : |(chi4 d : ℝ)| ≤ 1 := chi4_abs_le_one d
      have hq2 : 2 ≤ n / d := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr (by omega)
      have hW := W4_values (n / d)
      by_cases h4 : n / d ≤ 4
      · rw [hW.2.1 ⟨hq2, h4⟩]; simp; split_ifs <;> linarith
      · by_cases h6 : n / d ≤ 6
        · have h5 : 5 ≤ n / d := by omega
          have hd_in : d ∈ Finset.Icc (n / 7 + 1) (n / 5) := by
            simp only [Finset.mem_Icc]
            have ha : d ≤ n / 5 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 5)).mpr (by
              have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp h5; linarith)
            have hb : n / 7 < d := by
              have hlt : n < 7 * d := by
                have := (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).mp (by omega : n / d < 7)
                linarith
              omega
            omega
          rw [hW.2.2.1 ⟨h5, h6⟩, if_pos hd_in]
          have h1 : -((chi4 d : ℝ) * Λ d * (1 : ℤ)) ≤ Λ d := by
            have := (abs_le.mp hchi).1
            simp only [Int.cast_one, mul_one]
            nlinarith
          split_ifs <;> linarith
        · by_cases h9 : n / d ≤ 9
          · rw [hW.2.2.2.1 ⟨by omega, h9⟩]; simp; split_ifs <;> linarith
          · have h10 : 10 ≤ n / d := by omega
            have hd_in : d ∈ Finset.Icc 1 (n / 10) := by
              simp only [Finset.mem_Icc]
              have ha : d ≤ n / 10 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 10)).mpr (by
                have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp h10; linarith)
              exact ⟨hd1, ha⟩
            rw [if_pos hd_in]
            have hW2 : |(W4 (n / d) : ℝ)| ≤ 2 := by exact_mod_cast hW.2.2.2.2
            have hprod : |(chi4 d : ℝ) * (W4 (n / d) : ℝ)| ≤ 2 := by
              rw [abs_mul]
              nlinarith [abs_nonneg (chi4 d : ℝ), abs_nonneg (W4 (n / d) : ℝ)]
            have hneg : -((chi4 d : ℝ) * Λ d * (W4 (n / d) : ℝ)) ≤ 2 * Λ d := by
              have := (abs_le.mp hprod).1
              nlinarith
            split_ifs <;> linarith
    calc -(∑ d ∈ Finset.Icc 1 (n / 2), (chi4 d : ℝ) * Λ d * (W4 (n / d) : ℝ))
        = ∑ d ∈ Finset.Icc 1 (n / 2), -((chi4 d : ℝ) * Λ d * (W4 (n / d) : ℝ)) := by
          rw [Finset.sum_neg_distrib]
      _ ≤ ∑ d ∈ Finset.Icc 1 (n / 2),
            ((if d ∈ Finset.Icc (n / 7 + 1) (n / 5) then Λ d else 0) +
             (if d ∈ Finset.Icc 1 (n / 10) then 2 * Λ d else 0)) :=
          Finset.sum_le_sum hbound_term
      _ = (∑ d ∈ Finset.Icc 1 (n / 2), if d ∈ Finset.Icc (n / 7 + 1) (n / 5) then Λ d else 0) +
          (∑ d ∈ Finset.Icc 1 (n / 2), if d ∈ Finset.Icc 1 (n / 10) then 2 * Λ d else 0) :=
          Finset.sum_add_distrib
      _ = (ψ ((n / 5 : ℕ) : ℝ) - ψ ((n / 7 : ℕ) : ℝ)) + 2 * ψ ((n / 10 : ℕ) : ℝ) := by
          congr 1
          · rw [← Finset.sum_filter, psi_eq_sum_Icc, psi_eq_sum_Icc]
            have hfilt : (Finset.Icc 1 (n / 2)).filter (fun d => d ∈ Finset.Icc (n / 7 + 1) (n / 5)) =
                Finset.Icc (n / 7 + 1) (n / 5) := by
              ext d; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
            rw [hfilt]
            have hsub : Finset.Icc 1 (n / 7) ⊆ Finset.Icc 1 (n / 5) :=
              Finset.Icc_subset_Icc_right (by omega)
            rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
            congr 1
            ext d; simp only [Finset.mem_sdiff, Finset.mem_Icc]; omega
          · rw [← Finset.sum_filter, psi_eq_sum_Icc, Finset.mul_sum]
            have hfilt : (Finset.Icc 1 (n / 2)).filter (fun d => d ∈ Finset.Icc 1 (n / 10)) =
                Finset.Icc 1 (n / 10) := by
              ext d; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
            rw [hfilt]
  linarith

/- Step 5: Breusch theorem for n ≥ 10^7 and explicit prime chain for 7 ≤ n ≤ 10^7 -/

lemma sum_even_vonMangoldt_half_le (n : ℕ) (hn : 2 ≤ n) :
    ∑ d ∈ (Finset.Icc (n / 2 + 1) n).filter (fun d => d % 2 = 0), Λ d ≤ Real.log n := by
  let S := (Finset.Icc (n / 2 + 1) n).filter (fun d => d % 2 = 0 ∧ Λ d ≠ 0)
  have heq : ∑ d ∈ (Finset.Icc (n / 2 + 1) n).filter (fun d => d % 2 = 0), Λ d =
      ∑ d ∈ S, Λ d := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h2 : d % 2 = 0 <;> by_cases hL : Λ d = 0 <;> simp [h2, hL]
  rw [heq]
  have hsub : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have hpa : IsPrimePow a := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp ha'.2.2
    have hpb : IsPrimePow b := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hb'.2.2
    have h2a : ∃ k, a = 2 ^ k := by
      rcases hpa with ⟨p, k, hp, hk, rfl⟩
      have h2dvd : 2 ∣ p ^ k := Nat.dvd_of_mod_eq_zero ha'.2.1
      have h2p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2dvd
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.nat_prime).mp h2p |>.symm
      exact ⟨k, by rw [hp2]⟩
    have h2b : ∃ k, b = 2 ^ k := by
      rcases hpb with ⟨p, k, hp, hk, rfl⟩
      have h2dvd : 2 ∣ p ^ k := Nat.dvd_of_mod_eq_zero hb'.2.1
      have h2p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2dvd
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.nat_prime).mp h2p |>.symm
      exact ⟨k, by rw [hp2]⟩
    rcases h2a with ⟨ka, rfl⟩
    rcases h2b with ⟨kb, rfl⟩
    have ha_icc := Finset.mem_Icc.mp ha'.1
    have hb_icc := Finset.mem_Icc.mp hb'.1
    have hka_le : ka ≤ kb := by
      by_contra hlt
      have h1 : kb + 1 ≤ ka := by omega
      have h2 : 2 * 2 ^ kb ≤ 2 ^ ka := by
        calc 2 * 2 ^ kb = 2 ^ (kb + 1) := by rw [pow_succ, mul_comm]
          _ ≤ 2 ^ ka := Nat.pow_le_pow_right (by norm_num) h1
      omega
    have hkb_le : kb ≤ ka := by
      by_contra hlt
      have h1 : ka + 1 ≤ kb := by omega
      have h2 : 2 * 2 ^ ka ≤ 2 ^ kb := by
        calc 2 * 2 ^ ka = 2 ^ (ka + 1) := by rw [pow_succ, mul_comm]
          _ ≤ 2 ^ kb := Nat.pow_le_pow_right (by norm_num) h1
      omega
    have : ka = kb := le_antisymm hka_le hkb_le
    rw [this]
  have hle : ∀ d ∈ S, Λ d ≤ Real.log n := by
    intro d hd
    have hd_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
    exact (ArithmeticFunction.vonMangoldt_le_log).trans
      (Real.log_le_log (by exact_mod_cast (by omega : 0 < d)) (by exact_mod_cast hd_icc.2))
  calc ∑ d ∈ S, Λ d ≤ ∑ _d ∈ S, Real.log n := Finset.sum_le_sum hle
    _ = S.card * Real.log n := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * Real.log n := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hsub)
        exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    _ = Real.log n := one_mul _

lemma log_le_quarter_fourth_root (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) / 4 + 12 := by
  set y := Real.sqrt (Real.sqrt (n : ℝ))
  have hy_pos : 0 < y := by positivity
  have hy4 : y ^ 4 = (n : ℝ) := by
    have h1 : y ^ 2 = Real.sqrt (n : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (n : ℝ)) ^ 2 := by rw [h1]
      _ = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hlog_eq : Real.log (n : ℝ) = 4 * Real.log (y / 16) + 16 * Real.log 2 := by
    have h1 : (n : ℝ) = (y / 16) ^ 4 * (2 : ℝ) ^ 16 := by
      rw [← hy4]; ring
    rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h2 := Real.log_le_sub_one_of_pos (show 0 < y / 16 by positivity)
  linarith [log_two_bounds.2]

lemma poly_bound_56 (y : ℝ) (hy : 56 ≤ y) :
    y ^ 3 + 48 * y ^ 2 + 40 * (y / 4 + 12) ^ 2 + 17 * (y / 4 + 12) + 255 <
      (0.052 : ℝ) * y ^ 4 := by
  have h1 : 56 * y ≤ y ^ 2 := by nlinarith
  have h2 : 56 * y ^ 2 ≤ y ^ 3 := by nlinarith
  have h3 : 56 * y ^ 3 ≤ y ^ 4 := by nlinarith
  nlinarith

lemma exists_prime_mod_four_eq_three_large (n : ℕ) (hn : 10000000 ≤ n) :
    ∃ p, p.Prime ∧ p % 4 = 3 ∧ n / 2 < p ∧ p ≤ n := by
  -- Step A: Show 2 * ∑_{n/2 < d ≤ n, d % 4 = 3} Λ d > 2 * (ψ n - θ n)
  have hsplit_half :
      ψ (n : ℝ) - ψ ((n / 2 : ℕ) : ℝ) = ∑ d ∈ Finset.Icc (n / 2 + 1) n, Λ d := by
    rw [psi_eq_sum_Icc, psi_eq_sum_Icc]
    have hsub : Finset.Icc 1 (n / 2) ⊆ Finset.Icc 1 n :=
      Finset.Icc_subset_Icc_right (Nat.div_le_self n 2)
    rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
    congr 1; ext d; simp only [Finset.mem_sdiff, Finset.mem_Icc]; omega
  have h2psi3 :
      2 * (∑ d ∈ (Finset.Icc (n / 2 + 1) n).filter (fun d => d % 4 = 3), Λ d) =
      (∑ d ∈ Finset.Icc (n / 2 + 1) n, Λ d) -
      (∑ d ∈ (Finset.Icc (n / 2 + 1) n).filter (fun d => d % 2 = 0), Λ d) -
      (∑ d ∈ Finset.Icc (n / 2 + 1) n, (chi4 d : ℝ) * Λ d) := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum]
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [chi4]
    have hmod : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
    rcases hmod with h0 | h1 | h2 | h3
    · have he : d % 2 = 0 := by omega
      simp [h0, he]
    · have he : d % 2 ≠ 0 := by omega
      simp [h1, he]
    · have he : d % 2 = 0 := by omega
      simp [h2, he]
    · have he : d % 2 ≠ 0 := by omega
      simp [h3, he]; ring
  have hchi_le := chi4_half_interval_bound n (by omega)
  have heven_le := sum_even_vonMangoldt_half_le n (by omega)
  have hpsi_n := psi_ge_tight n (by omega)
  have hpsi_2 := psi_le_tight (n / 2) (by omega)
  have hpsi_5 := psi_le_tight (n / 5) (by omega)
  have hpsi_7 := psi_ge_tight (n / 7) (by omega)
  have hpsi_10 := psi_le_tight (n / 10) (by omega)
  have hlog_div : ∀ k : ℕ, 1 ≤ k → k ≤ n → Real.log ((n / k : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
    intro k hk hkn
    apply Real.log_le_log
    · exact_mod_cast ((Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr (by omega) : 1 ≤ n / k)
    · exact_mod_cast Nat.div_le_self n k
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hlog_div_nn : ∀ k : ℕ, 1 ≤ k → k ≤ n → 0 ≤ Real.log ((n / k : ℕ) : ℝ) := by
    intro k hk hkn
    exact Real.log_nonneg (by exact_mod_cast ((Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr (by omega) : 1 ≤ n / k))
  have hsq_div : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      (Real.log ((n / k : ℕ) : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
    intro k hk hkn
    have h1 := hlog_div k hk hkn
    have h2 := hlog_div_nn k hk hkn
    nlinarith
  have hdiv_le_real : ∀ k : ℕ, 1 ≤ k → ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / k := by
    intro k hk
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < k)]
    exact_mod_cast Nat.div_mul_le_self n k
  have hdiv7_ge : (n : ℝ) / 7 - 1 ≤ ((n / 7 : ℕ) : ℝ) := by
    have : n < n / 7 * 7 + 7 := by omega
    have h1 : (n : ℝ) < ((n / 7 : ℕ) : ℝ) * 7 + 7 := by exact_mod_cast this
    linarith
  have h2psi3_ge :
      (0.052 : ℝ) * n - 40 * (Real.log n) ^ 2 - 17 * Real.log n - 255 ≤
      2 * (∑ d ∈ (Finset.Icc (n / 2 + 1) n).filter (fun d => d % 4 = 3), Λ d) := by
    have h2d := hdiv_le_real 2 (by norm_num)
    have h5d := hdiv_le_real 5 (by norm_num)
    have h10d := hdiv_le_real 10 (by norm_num)
    have hsq2 := hsq_div 2 (by norm_num) (by omega)
    have hsq5 := hsq_div 5 (by norm_num) (by omega)
    have hsq10 := hsq_div 10 (by norm_num) (by omega)
    have hlog7 := hlog_div 7 (by norm_num) (by omega)
    linarith
  -- Compare with 2 * (ψ n - θ n) ≤ 4 * sqrt n * log n
  have hpsi_theta : ψ (n : ℝ) - θ (n : ℝ) ≤ 2 * Real.sqrt n * Real.log n :=
    le_trans (le_abs_self _) (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by exact_mod_cast (by omega : 1 ≤ n)))
  -- Show 0.052 * n - 40 * (log n)^2 - 17 * log n - 255 > 4 * sqrt n * log n for n ≥ 10^7
  have hpos :
      4 * Real.sqrt n * Real.log n <
      (0.052 : ℝ) * n - 40 * (Real.log n) ^ 2 - 17 * Real.log n - 255 := by
    set y := Real.sqrt (Real.sqrt (n : ℝ))
    have hy_ge : (56 : ℝ) ≤ y := by
      have h1 : (56 : ℝ) ^ 4 ≤ (n : ℝ) := by
        have : (56 : ℝ) ^ 4 = 9834496 := by norm_num
        have hn' : (10000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have h2 : (56 : ℝ) ^ 2 ≤ Real.sqrt (n : ℝ) := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]
        nlinarith
      rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)]
      exact h2
    have hsq_eq : Real.sqrt (n : ℝ) = y ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
    have hn_eq : (n : ℝ) = y ^ 4 := by
      rw [← Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n), hsq_eq]; ring
    have hlog_ub : Real.log (n : ℝ) ≤ y / 4 + 12 := log_le_quarter_fourth_root n (by omega)
    have hlog_sq_ub : (Real.log (n : ℝ)) ^ 2 ≤ (y / 4 + 12) ^ 2 := by nlinarith
    have hmul_ub : 4 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ 4 * y ^ 2 * (y / 4 + 12) := by
      rw [hsq_eq]
      have : 0 ≤ 4 * y ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left hlog_ub this
    -- Need 0.052 * y^4 > y^3 + 48 * y^2 + 40*(y/4 + 12)^2 + 17*(y/4 + 12) + 255
    -- = y^3 + 50.5 * y^2 + 244.25 * y + 6219
    -- For y ≥ 56: 0.052*y^4 - y^3 - 50.5*y^2 - 244.25*y - 6219
    -- = y^2*(0.052*y^2 - y - 50.5) - 244.25*y - 6219
    -- At y ≥ 56: 0.052*y^2 - y - 50.5 ≥ 0.052*56*y - y - 50.5 = 1.912*y - 50.5 ≥ 56.5
    -- So y^2*(...) ≥ 56.5 * 56 * y = 3164 * y > 244.25 * y + 6219!
    have hpoly := poly_bound_56 y hy_ge
    linarith [hn_eq, hlog_ub, hlog_sq_ub, hmul_ub, hpoly]
  have hgt_diff :
      ψ (n : ℝ) - θ (n : ℝ) <
      ∑ d ∈ (Finset.Icc (n / 2 + 1) n).filter (fun d => d % 4 = 3), Λ d := by
    linarith
  -- If no prime p ≡ 3 mod 4 in (n/2, n], then every nonzero term in the sum is a prime power p^k (k ≥ 2),
  -- whose total contribution is ≤ ψ n - θ n!
  by_contra hno
  push_neg at hno
  have hle_diff :
      ∑ d ∈ (Finset.Icc (n / 2 + 1) n).filter (fun d => d % 4 = 3), Λ d ≤
      ψ (n : ℝ) - θ (n : ℝ) := by
    have htheta_eq : θ (n : ℝ) = ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log p := by
      rw [Chebyshev.theta_eq_sum_Icc]
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.floor_natCast]
      constructor
      · intro ⟨⟨_, hle⟩, hp⟩; exact ⟨⟨hp.one_lt.le, hle⟩, hp⟩
      · intro ⟨⟨_, hle⟩, hp⟩; exact ⟨⟨Nat.zero_le p, hle⟩, hp⟩
    rw [psi_eq_sum_Icc, htheta_eq]
    have htheta : (∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log p) =
        ∑ d ∈ (Finset.Icc 1 n).filter Nat.Prime, Λ d := by
      refine Finset.sum_congr rfl fun p hp => ?_
      exact (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2).symm
    have hdiff_eq : (∑ d ∈ Finset.Icc 1 n, Λ d) - ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log p =
        ∑ d ∈ (Finset.Icc 1 n).filter (fun d => ¬ d.Prime), Λ d := by
      have h2 := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) Nat.Prime (fun d => Λ d)
      linarith
    rw [hdiff_eq]
    have hsub : (Finset.Icc (n / 2 + 1) n).filter (fun d => d % 4 = 3) ⊆
        (Finset.Icc 1 n).filter (fun d => ¬ d.Prime) := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
      refine ⟨⟨by omega, hd.1.2⟩, fun hpr => ?_⟩
      exact absurd hd.1.2 (not_le_of_gt (hno d hpr hd.2 (by omega)))
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
  linarith

lemma exists_prime_mod_four_eq_three_medium (n : ℕ) (hlo : 7 ≤ n) (hhi : n < 10000000) :
    ∃ p, p.Prime ∧ p % 4 = 3 ∧ n / 2 < p ∧ p ≤ n := by
  have hcheck : ∀ p : ℕ, p.Prime → p % 4 = 3 → p ≤ n → n < 2 * p →
      ∃ q, q.Prime ∧ q % 4 = 3 ∧ n / 2 < q ∧ q ≤ n :=
    fun p hp hp3 hle hlt => ⟨p, hp, hp3, by omega, hle⟩
  by_cases h1 : n < 14
  · exact hcheck 7 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h2 : n < 22
  · exact hcheck 11 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h3 : n < 38
  · exact hcheck 19 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h4 : n < 62
  · exact hcheck 31 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h5 : n < 118
  · exact hcheck 59 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h6 : n < 214
  · exact hcheck 107 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h7 : n < 422
  · exact hcheck 211 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h8 : n < 838
  · exact hcheck 419 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h9 : n < 1654
  · exact hcheck 827 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h10 : n < 3254
  · exact hcheck 1627 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h11 : n < 6502
  · exact hcheck 3251 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h12 : n < 12982
  · exact hcheck 6491 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h13 : n < 25958
  · exact hcheck 12979 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h14 : n < 51902
  · exact hcheck 25951 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h15 : n < 103798
  · exact hcheck 51899 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h16 : n < 207574
  · exact hcheck 103787 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h17 : n < 415126
  · exact hcheck 207563 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h18 : n < 830222
  · exact hcheck 415111 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h19 : n < 1660382
  · exact hcheck 830191 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h20 : n < 3320734
  · exact hcheck 1660367 (by norm_num) (by norm_num) (by omega) (by omega)
  by_cases h21 : n < 6641398
  · exact hcheck 3320699 (by norm_num) (by norm_num) (by omega) (by omega)
  exact hcheck 6641387 (by norm_num) (by norm_num) (by omega) (by omega)

lemma exists_prime_mod_four_eq_three_ge_seven (n : ℕ) (hn : 7 ≤ n) :
    ∃ p, p.Prime ∧ p % 4 = 3 ∧ n / 2 < p ∧ p ≤ n := by
  by_cases h : n < 10000000
  · exact exists_prime_mod_four_eq_three_medium n hn h
  · exact exists_prime_mod_four_eq_three_large n (by omega)

end OMA.Erdos399Proof

theorem OMA.solution : type_of% @Erdos399.erdos_399.variants.sum_two_squares := by
  intro n x y hxy hfact
  by_cases hn7 : 7 ≤ n
  · obtain ⟨p, hp, hp3, hlo, hhi⟩ := OMA.Erdos399Proof.exists_prime_mod_four_eq_three_ge_seven n hn7
    exact absurd hfact (OMA.Erdos399Proof.not_factorial_eq_sq_add_sq_of_prime_in_interval hp hp3 hlo hhi)
  have hlt7 : n < 7 := by omega
  interval_cases n
  · simp [Nat.factorial] at hfact; nlinarith
  · simp [Nat.factorial] at hfact; nlinarith
  · simp [Nat.factorial] at hfact; nlinarith
  · simp [Nat.factorial] at hfact
    have hx : x ≤ 2 := by nlinarith
    have hy : y ≤ 2 := by nlinarith
    interval_cases x <;> interval_cases y <;> omega
  · simp [Nat.factorial] at hfact
    have hx : x ≤ 4 := by nlinarith
    have hy : y ≤ 4 := by nlinarith
    interval_cases x <;> interval_cases y <;> omega
  · simp [Nat.factorial] at hfact
    have hx : x ≤ 10 := by nlinarith
    have hy : y ≤ 10 := by nlinarith
    interval_cases x <;> interval_cases y <;> omega
  · refine ⟨rfl, ?_⟩
    have h720 : 720 = x ^ 2 + y ^ 2 := by simpa [Nat.factorial] using hfact
    have hx : x ≤ 26 := by nlinarith
    have hy : y ≤ 26 := by nlinarith
    have hdec : ∀ a b : Fin 27, 1 < a.val * b.val → 720 = a.val ^ 2 + b.val ^ 2 →
        (a.val = 12 ∧ b.val = 24) ∨ (a.val = 24 ∧ b.val = 12) := by decide
    exact hdec ⟨x, by omega⟩ ⟨y, by omega⟩ hxy h720
