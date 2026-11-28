import OMAReductions.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1
import Mathlib

/-!
# First moment of the preliminary sieve

We prove the elementary first-moment bounds and range estimates for the
preliminary sieve step. The proof is completely elementary:
1. Chebyshev's 1852 factorial identity with the period-30 weight
   `n - ⌊n/2⌋ - ⌊n/3⌋ - ⌊n/5⌋ + ⌊n/30⌋` gives explicit bounds
   `0.91 x - O(log x) ≤ ψ(x) ≤ 1.116 x + O((log x)^2)`, which via Mathlib's
   `Chebyshev` module yields `0.89 x / log x ≤ π(⌊x⌋) ≤ 1.13 x / log x`
   eventually.
2. Mertens' first and second theorems via Legendre's formula and summation
   by parts give `∏_{u < p ≤ v} (1 - 1/p) ~ log u / log v`.
3. Combining these with elementary logarithmic asymptotics places
   `M = |V| · ∏_{p ∈ S} (1 - 1/p)` strictly inside `[60, 100] · c X U / log X`
   and establishes all auxiliary range and exponential inequalities.
-/
-- Credit: @carterleffen

open Filter Topology Finset Real
open scoped Asymptotics

namespace PreliminarySieveMoment

private lemma stirling_lower (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hn0.le n
  rw [div_le_iff₀ hf] at h
  have h' := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at h'
  linarith

private lemma stirling_upper (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) - n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hfpos : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [hfac, Real.log_mul hk1.ne' hfpos.ne']
    have hlog := Real.log_le_sub_one_of_pos (show 0 < ((k : ℝ) + 1) / ((k : ℝ) + 2) by positivity)
    rw [Real.log_div hk1.ne' hk2.ne'] at hlog
    have hstep : 1 ≤ ((k : ℝ) + 2) * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) := by
      have h1 : 1 / ((k : ℝ) + 2) ≤ Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) := by
        have e : ((k : ℝ) + 1) / ((k : ℝ) + 2) - 1 = -(1 / ((k : ℝ) + 2)) := by field_simp; ring
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hk2.le
      rwa [mul_one_div_cancel hk2.ne'] at h2
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have e2 : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
    rw [e2]
    linarith

private lemma log_factorial_div_bounds (n k : ℕ) (hk : 1 ≤ k) (hn : k ≤ n) :
    let t := (n : ℝ) / k
    t * Real.log t - t - Real.log n ≤ Real.log ((n / k).factorial : ℝ) ∧
    Real.log ((n / k).factorial : ℝ) ≤ t * Real.log t - t + Real.log ((n : ℝ) + 1) + 2 := by
  intro t
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (hk.trans hn)
  have ht1 : (1 : ℝ) ≤ t := (one_le_div hk0).mpr (by exact_mod_cast hn)
  have htn : t ≤ n := div_le_self hn0.le (by exact_mod_cast hk)
  have hm1 : 1 ≤ n / k := Nat.div_pos hn hk
  have hm0 : (0 : ℝ) < (n / k : ℕ) := by exact_mod_cast hm1
  have hm_le : ((n / k : ℕ) : ℝ) ≤ t := Nat.cast_div_le
  have hm_gt : t - 1 < ((n / k : ℕ) : ℝ) := by
    have hdiv : (n : ℝ) < ((n / k : ℕ) : ℝ) * k + k := by
      exact_mod_cast Nat.lt_div_mul_add hk
    have : t < ((n / k : ℕ) : ℝ) + 1 := (div_lt_iff₀ hk0).mpr (by linarith)
    linarith
  constructor
  · have hlow := stirling_lower (n / k) hm1
    have hratio := Real.log_le_sub_one_of_pos (show 0 < t / ((n / k : ℕ) : ℝ) by positivity)
    rw [Real.log_div (by positivity) hm0.ne'] at hratio
    have hmul : ((n / k : ℕ) : ℝ) * (Real.log t - Real.log ((n / k : ℕ) : ℝ)) ≤
        t - ((n / k : ℕ) : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hratio hm0.le
      have e : ((n / k : ℕ) : ℝ) * (t / ((n / k : ℕ) : ℝ) - 1) = t - ((n / k : ℕ) : ℝ) := by
        field_simp
      linarith
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
    have htm : (t - ((n / k : ℕ) : ℝ)) * Real.log t ≤ Real.log n := by
      calc (t - ((n / k : ℕ) : ℝ)) * Real.log t
          ≤ 1 * Real.log t := mul_le_mul_of_nonneg_right (by linarith) hlogt
        _ = Real.log t := one_mul _
        _ ≤ Real.log n := Real.log_le_log (by positivity) htn
    linarith
  · have hup := stirling_upper (n / k)
    have hmon : (((n / k : ℕ) : ℝ) + 1) * Real.log (((n / k : ℕ) : ℝ) + 1) ≤
        (t + 1) * Real.log (t + 1) := by
      apply mul_le_mul (by linarith) (Real.log_le_log (by positivity) (by linarith))
        (Real.log_nonneg (by linarith)) (by positivity)
    have hratio := Real.log_le_sub_one_of_pos (show 0 < (t + 1) / t by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at hratio
    have hmul : t * (Real.log (t + 1) - Real.log t) ≤ 1 := by
      have h1 := mul_le_mul_of_nonneg_left hratio (by positivity : (0 : ℝ) ≤ t)
      have e : t * ((t + 1) / t - 1) = 1 := by field_simp; ring
      linarith
    have hlogn : Real.log (t + 1) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith

private lemma log_factorial_eq_sum_log (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ m ∈ Finset.Icc 1 n, Real.log (m : ℝ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih]
    have hfac : ((k + 1).factorial : ℝ) = ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac, Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_pos k).ne'), add_comm]

private lemma card_filter_dvd_Icc (n d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Icc 1 n).filter (fun m => d ∣ m)).card = n / d := by
  have heq : (Finset.Icc 1 n).filter (fun m => d ∣ m) =
      (Finset.Icc 1 (n / d)).image (fun k => k * d) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hm1, hmn⟩, k, rfl⟩
      refine ⟨k, ⟨?_, ?_⟩, mul_comm k d⟩
      · by_contra hk0
        have : k = 0 := by omega
        subst this; omega
      · rw [Nat.le_div_iff_mul_le hd]
        linarith
    · rintro ⟨k, ⟨hk1, hkd⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, k, mul_comm k d⟩
      · exact Nat.mul_le_mul hk1 hd
      · exact (Nat.le_div_iff_mul_le hd).mp hkd
  rw [heq, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    exact Nat.eq_of_mul_eq_mul_right hd hab

private lemma log_factorial_eq_sum_vonMangoldt (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d * ((n / d : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum_log]
  have h1 : ∑ m ∈ Finset.Icc 1 n, Real.log (m : ℝ) =
      ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
        if d ∣ m then ArithmeticFunction.vonMangoldt d else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [← ArithmeticFunction.vonMangoldt_sum, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdm, hm0⟩
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdm (by omega)
      have hdn : d ≤ n := (Nat.le_of_dvd (by omega) hdm).trans hm.2
      exact ⟨⟨hd1, hdn⟩, hdm⟩
    · rintro ⟨_, hdm⟩
      exact ⟨hdm, by omega⟩
  rw [h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_Icc] at hd
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_filter_dvd_Icc n d hd.1, mul_comm]

private def chebCoeff (q : ℕ) : ℤ :=
  (q : ℤ) - (q / 2 : ℕ) - (q / 3 : ℕ) - (q / 5 : ℕ) + (q / 30 : ℕ)

private lemma chebCoeff_nonneg (q : ℕ) : 0 ≤ chebCoeff q := by
  unfold chebCoeff; omega

private lemma chebCoeff_le_one (q : ℕ) : chebCoeff q ≤ 1 := by
  unfold chebCoeff; omega

private lemma chebCoeff_eq_one {q : ℕ} (h1 : 1 ≤ q) (h5 : q ≤ 5) : chebCoeff q = 1 := by
  unfold chebCoeff; omega

private noncomputable def chebB (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) - Real.log ((n / 2).factorial : ℝ) -
    Real.log ((n / 3).factorial : ℝ) - Real.log ((n / 5).factorial : ℝ) +
    Real.log ((n / 30).factorial : ℝ)

private lemma log_factorial_div_sum_extend (n k : ℕ) :
    Real.log ((n / k).factorial : ℝ) =
      ∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d * (((n / d) / k : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum_vonMangoldt]
  have hsub : Finset.Icc 1 (n / k) ⊆ Finset.Icc 1 n :=
    Finset.Icc_subset_Icc_right (Nat.div_le_self n k)
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro d _
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm k d]
  · intro d hd_in hd
    rw [Finset.mem_Icc] at hd hd_in
    have hgt : n / k < d := by omega
    have hzero : (n / d) / k = 0 := by
      rw [Nat.div_div_eq_div_mul, mul_comm d k, ← Nat.div_div_eq_div_mul]
      exact Nat.div_eq_of_lt hgt
    simp [hzero]

private lemma chebB_eq_sum (n : ℕ) :
    chebB n = ∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d * (chebCoeff (n / d) : ℝ) := by
  unfold chebB
  rw [log_factorial_eq_sum_vonMangoldt,
    log_factorial_div_sum_extend n 2,
    log_factorial_div_sum_extend n 3,
    log_factorial_div_sum_extend n 5,
    log_factorial_div_sum_extend n 30]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  simp only [chebCoeff, Int.cast_add, Int.cast_sub, Int.cast_natCast]
  ring

private lemma psi_nat_eq_sum_Icc (n : ℕ) :
    Chebyshev.psi (n : ℝ) = ∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d := by
  rw [Chebyshev.psi, Nat.floor_natCast]
  rfl

private lemma chebB_le_psi (n : ℕ) : chebB n ≤ Chebyshev.psi (n : ℝ) := by
  rw [chebB_eq_sum, psi_nat_eq_sum_Icc]
  apply Finset.sum_le_sum
  intro d _
  have h1 : (chebCoeff (n / d) : ℝ) ≤ 1 := by exact_mod_cast chebCoeff_le_one (n / d)
  have hL : 0 ≤ ArithmeticFunction.vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
  nlinarith

private lemma psi_sub_psi_div_six_le_chebB (n : ℕ) :
    Chebyshev.psi (n : ℝ) - Chebyshev.psi ((n / 6 : ℕ) : ℝ) ≤ chebB n := by
  rw [psi_nat_eq_sum_Icc, psi_nat_eq_sum_Icc, chebB_eq_sum]
  have hsub : Finset.Icc 1 (n / 6) ⊆ Finset.Icc 1 n :=
    Finset.Icc_subset_Icc_right (Nat.div_le_self n 6)
  rw [← Finset.sum_sdiff_eq_sub hsub]
  have hsub2 : Finset.Icc 1 n \ Finset.Icc 1 (n / 6) ⊆ Finset.Icc 1 n := Finset.sdiff_subset
  calc ∑ d ∈ Finset.Icc 1 n \ Finset.Icc 1 (n / 6), ArithmeticFunction.vonMangoldt d
      = ∑ d ∈ Finset.Icc 1 n \ Finset.Icc 1 (n / 6),
          ArithmeticFunction.vonMangoldt d * (chebCoeff (n / d) : ℝ) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc] at hd
        have hd1 : 1 ≤ d := hd.1.1
        have hdn : d ≤ n := hd.1.2
        have hd6 : n / 6 < d := by omega
        have hq1 : 1 ≤ n / d := Nat.div_pos hdn hd1
        have hq5 : n / d ≤ 5 := by
          have : n < 6 * d := by omega
          have : n / d < 6 := (Nat.div_lt_iff_lt_mul hd1).mpr (by linarith)
          omega
        rw [chebCoeff_eq_one hq1 hq5]
        simp
    _ ≤ ∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d * (chebCoeff (n / d) : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub2
        intro d _ _
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (by exact_mod_cast chebCoeff_nonneg (n / d))

private noncomputable def chebA : ℝ :=
  (7 / 15 : ℝ) * Real.log 2 + (3 / 10 : ℝ) * Real.log 3 + (1 / 6 : ℝ) * Real.log 5

private lemma chebA_bounds : (91 / 100 : ℝ) < chebA ∧ chebA < (93 / 100 : ℝ) := by
  have h2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h2hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have h3lo : 11 * Real.log 2 < 7 * Real.log 3 := by
    have h := Real.log_lt_log (by norm_num) (show ((2 : ℝ) ^ 11) < ((3 : ℝ) ^ 7) by norm_num)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    exact h
  have h3hi : 5 * Real.log 3 < 8 * Real.log 2 := by
    have h := Real.log_lt_log (by norm_num) (show ((3 : ℝ) ^ 5) < ((2 : ℝ) ^ 8) by norm_num)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    exact h
  have h5lo : 9 * Real.log 2 < 4 * Real.log 5 := by
    have h := Real.log_lt_log (by norm_num) (show ((2 : ℝ) ^ 9) < ((5 : ℝ) ^ 4) by norm_num)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    exact h
  have h5hi : 3 * Real.log 5 < 7 * Real.log 2 := by
    have h := Real.log_lt_log (by norm_num) (show ((5 : ℝ) ^ 3) < ((2 : ℝ) ^ 7) by norm_num)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    exact h
  unfold chebA
  constructor <;> linarith

private lemma chebB_asymp (n : ℕ) (hn : 30 ≤ n) :
    chebA * n - (5 * Real.log ((n : ℝ) + 1) + 10) ≤ chebB n ∧
    chebB n ≤ chebA * n + (5 * Real.log ((n : ℝ) + 1) + 10) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 := log_factorial_div_bounds n 1 (by omega) (by omega)
  have h2 := log_factorial_div_bounds n 2 (by omega) (by omega)
  have h3 := log_factorial_div_bounds n 3 (by omega) (by omega)
  have h5 := log_factorial_div_bounds n 5 (by omega) (by omega)
  have h30 := log_factorial_div_bounds n 30 (by omega) hn
  dsimp only at h1 h2 h3 h5 h30
  have hn1 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hn0 (by linarith)
  have hlog30 : Real.log (30 : ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
    have : (30 : ℝ) = 2 * 3 * 5 := by norm_num
    rw [this, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  have hd2 : Real.log ((n : ℝ) / 2) = Real.log n - Real.log 2 :=
    Real.log_div hn0.ne' (by norm_num)
  have hd3 : Real.log ((n : ℝ) / 3) = Real.log n - Real.log 3 :=
    Real.log_div hn0.ne' (by norm_num)
  have hd5 : Real.log ((n : ℝ) / 5) = Real.log n - Real.log 5 :=
    Real.log_div hn0.ne' (by norm_num)
  have hd30 : Real.log ((n : ℝ) / 30) = Real.log n - Real.log 30 :=
    Real.log_div hn0.ne' (by norm_num)
  simp only [Nat.div_one, Nat.cast_one, div_one, Nat.cast_ofNat, hd2, hd3, hd5, hd30, hlog30] at h1 h2 h3 h5 h30
  have halg :
      ((n : ℝ) * Real.log n - n) -
      ((n : ℝ) / 2 * (Real.log n - Real.log 2) - (n : ℝ) / 2) -
      ((n : ℝ) / 3 * (Real.log n - Real.log 3) - (n : ℝ) / 3) -
      ((n : ℝ) / 5 * (Real.log n - Real.log 5) - (n : ℝ) / 5) +
      ((n : ℝ) / 30 * (Real.log n - (Real.log 2 + Real.log 3 + Real.log 5)) - (n : ℝ) / 30) =
      chebA * n := by
    unfold chebA; ring
  unfold chebB
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h5.1, h5.2, h30.1, h30.2]

private lemma psi_ge_cheb (n : ℕ) (hn : 30 ≤ n) :
    (91 / 100 : ℝ) * n - (5 * Real.log ((n : ℝ) + 1) + 10) ≤ Chebyshev.psi (n : ℝ) := by
  have hB := (chebB_asymp n hn).1
  have hle := chebB_le_psi n
  have hA := chebA_bounds.1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

private lemma psi_le_cheb (n : ℕ) :
    Chebyshev.psi (n : ℝ) ≤ (1116 / 1000 : ℝ) * n + 20 * (Real.log ((n : ℝ) + 2)) ^ 2 + 200 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 30
    · have hbase := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)
      have hlog4 : Real.log 4 ≤ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, Nat.cast_ofNat]
        linarith [Real.log_two_lt_d9]
      have hn30 : (n : ℝ) ≤ 30 := by exact_mod_cast hn.le
      have h1 : (Real.log 4 + 4) * (n : ℝ) ≤ 180 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have h2 : 0 ≤ (1116 / 1000 : ℝ) * n + 20 * (Real.log ((n : ℝ) + 2)) ^ 2 := by positivity
      linarith
    · have hn : 30 ≤ n := by omega
      have hstep := psi_sub_psi_div_six_le_chebB n
      have hB := (chebB_asymp n hn).2
      have hA := chebA_bounds.2
      have hlt : n / 6 < n := Nat.div_lt_self (by omega) (by omega)
      have hih := ih (n / 6) hlt
      have hdiv_le : ((n / 6 : ℕ) : ℝ) ≤ (n : ℝ) / 6 := by
        simpa using (Nat.cast_div_le (m := n) (n := 6) (α := ℝ))
      have hlog_step : Real.log (((n / 6 : ℕ) : ℝ) + 2) ≤ Real.log ((n : ℝ) + 2) - Real.log 2 := by
        have hle2 : 2 * (((n / 6 : ℕ) : ℝ) + 2) ≤ (n : ℝ) + 2 := by
          have : (30 : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        have hpos : 0 < ((n / 6 : ℕ) : ℝ) + 2 := by positivity
        have hlg := Real.log_le_log (by positivity) hle2
        rw [Real.log_mul (by norm_num) hpos.ne'] at hlg
        linarith
      have hlog_nn : 0 ≤ Real.log (((n / 6 : ℕ) : ℝ) + 2) :=
        Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (n / 6)])
      have hlog_big : 5 * Real.log 2 ≤ Real.log ((n : ℝ) + 2) := by
        have h32 : ((2 : ℝ) ^ 5) ≤ (n : ℝ) + 2 := by
          have : (30 : ℝ) ≤ n := by exact_mod_cast hn
          norm_num; linarith
        have hlg := Real.log_le_log (by positivity) h32
        rwa [Real.log_pow, Nat.cast_ofNat] at hlg
      have hsq : Real.log 2 * Real.log ((n : ℝ) + 2) ≤
          (Real.log ((n : ℝ) + 2)) ^ 2 - (Real.log (((n / 6 : ℕ) : ℝ) + 2)) ^ 2 := by
        have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        nlinarith
      have hlog12 : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have h2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hcomb : 5 * Real.log ((n : ℝ) + 1) + 10 ≤
          20 * ((Real.log ((n : ℝ) + 2)) ^ 2 - (Real.log (((n / 6 : ℕ) : ℝ) + 2)) ^ 2) := by
        nlinarith
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith

private lemma eventually_theta_cheb_bounds :
    ∀ᶠ x : ℝ in atTop, (90 / 100 : ℝ) * x ≤ Chebyshev.theta x ∧
      Chebyshev.theta x ≤ (112 / 100 : ℝ) * x := by
  have hadd2 : Tendsto (fun x : ℝ => x + 2) atTop atTop :=
    tendsto_id.atTop_add tendsto_const_nhds
  have hlog_o : (fun x : ℝ => Real.log (x + 2)) =o[atTop] (id : ℝ → ℝ) := by
    have h1 := Real.isLittleO_log_id_atTop.comp_tendsto hadd2
    refine h1.trans_isBigO ?_
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    simp only [Function.comp_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x + 2),
      abs_of_nonneg (by linarith : 0 ≤ x)]
    linarith
  have hlog2_o : (fun x : ℝ => (Real.log (x + 2)) ^ 2) =o[atTop] (id : ℝ → ℝ) := by
    have h1 := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).comp_tendsto hadd2
    have h2 : (fun x : ℝ => (Real.log (x + 2)) ^ 2) =ᶠ[atTop]
        (fun x : ℝ => (Real.log (x + 2)) ^ (2 : ℝ)) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x _
      exact (Real.rpow_two _).symm
    have h3 : (fun x : ℝ => (x + 2) ^ (1 : ℝ)) =O[atTop] (id : ℝ → ℝ) := by
      refine Asymptotics.IsBigO.of_bound 2 ?_
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      rw [Real.rpow_one]
      simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x + 2),
        abs_of_nonneg (by linarith : 0 ≤ x)]
      linarith
    exact (h1.congr' h2.symm EventuallyEq.rfl).trans_isBigO h3
  have hsqrt_o : Real.sqrt =o[atTop] (id : ℝ → ℝ) := by
    refine Asymptotics.isLittleO_iff.mpr fun ε hε => ?_
    filter_upwards [eventually_ge_atTop ((1 / ε) ^ 2)] with x hx
    have hx0 : 0 ≤ x := (sq_nonneg _).trans hx
    have h1 : 1 / ε ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hx
    have h2 : 1 ≤ ε * Real.sqrt x := by
      rw [div_le_iff₀ hε] at h1; linarith
    simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0, abs_of_nonneg (Real.sqrt_nonneg x)]
    calc Real.sqrt x = 1 * Real.sqrt x := (one_mul _).symm
      _ ≤ (ε * Real.sqrt x) * Real.sqrt x := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg x)
      _ = ε * x := by rw [mul_assoc, Real.mul_self_sqrt hx0]
  have hdiff_o := Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrt_o
  filter_upwards [eventually_ge_atTop (100000 : ℝ),
    hlog_o.bound (show (0 : ℝ) < 1 / 2000 by norm_num),
    hlog2_o.bound (show (0 : ℝ) < 1 / 10000 by norm_num),
    hdiff_o.bound (show (0 : ℝ) < 1 / 1000 by norm_num)] with x hx hlo hlo2 hdo
  have hx0 : 0 ≤ x := by linarith
  have hfl30 : 30 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hfl_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hfl_gt : x - 1 < (⌊x⌋₊ : ℝ) := Nat.sub_one_lt_floor x
  have hpsi_eq : Chebyshev.psi x = Chebyshev.psi (⌊x⌋₊ : ℝ) := Chebyshev.psi_eq_psi_coe_floor x
  have hpsi_lo := psi_ge_cheb ⌊x⌋₊ hfl30
  have hpsi_hi := psi_le_cheb ⌊x⌋₊
  have htheta_le : Chebyshev.theta x ≤ Chebyshev.psi x := Chebyshev.theta_le_psi x
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0, Pi.sub_apply] at hlo hlo2 hdo
  have hlg_nn : 0 ≤ Real.log (x + 2) := Real.log_nonneg (by linarith)
  rw [abs_of_nonneg hlg_nn] at hlo
  rw [abs_of_nonneg (sq_nonneg _)] at hlo2
  have hdiff_le : Chebyshev.psi x - Chebyshev.theta x ≤ (1 / 1000 : ℝ) * x :=
    (le_abs_self _).trans hdo
  have hlog_fl1 : Real.log ((⌊x⌋₊ : ℝ) + 1) ≤ Real.log (x + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog_fl2 : Real.log ((⌊x⌋₊ : ℝ) + 2) ≤ Real.log (x + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsq_fl2 : (Real.log ((⌊x⌋₊ : ℝ) + 2)) ^ 2 ≤ (Real.log (x + 2)) ^ 2 :=
    pow_le_pow_left₀ (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) ⌊x⌋₊])) hlog_fl2 2
  constructor <;> linarith

private lemma eventually_primeCounting_cheb_bounds :
    ∀ᶠ x : ℝ in atTop,
      (89 / 100 : ℝ) * (x / Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (113 / 100 : ℝ) * (x / Real.log x) := by
  have hint := Chebyshev.integral_theta_div_log_sq_isLittleO.bound (show (0 : ℝ) < 1 / 100 by norm_num)
  filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_theta_cheb_bounds, hint]
    with x hx ⟨hth_lo, hth_hi⟩ hi
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hrat_nn : 0 ≤ x / Real.log x := div_nonneg (by linarith) hlog_pos.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hrat_nn] at hi
  rw [abs_le] at hi
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral (by linarith)]
  have hlo : (90 / 100 : ℝ) * (x / Real.log x) ≤ Chebyshev.theta x / Real.log x := by
    rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hth_lo hlog_pos.le
  have hhi : Chebyshev.theta x / Real.log x ≤ (112 / 100 : ℝ) * (x / Real.log x) := by
    rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hth_hi hlog_pos.le
  constructor <;> linarith

private lemma log_factorial_eq_sum_primesLE (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE n, ((n.factorial).factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset
  · intro p hp
    rw [Nat.support_factorization] at hp
    rw [Nat.mem_primesLE]
    have hpp := Nat.prime_of_mem_primeFactors hp
    exact ⟨hpp.dvd_factorial.mp (Nat.dvd_of_mem_primeFactors hp), hpp⟩
  · intro p _ hp
    rw [Finsupp.notMem_support_iff] at hp
    simp [hp]

private lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ (n.factorial).factorization p := by
  rw [Nat.factorization_factorial hp (b := n + 1) (Nat.lt_succ_of_le (Nat.log_le_self p n))]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : 1 ∈ Finset.Ico 1 (n + 1) := by rw [Finset.mem_Ico]; omega
    have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1
    simpa using this

private lemma mertens_first_upper (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
      (by exact_mod_cast Nat.factorial_le_pow n)
  have h2 : ∑ p ∈ Nat.primesLE n, ((n : ℝ) / p - 1) * Real.log p ≤
      Real.log (n.factorial : ℝ) := by
    rw [log_factorial_eq_sum_primesLE]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    apply mul_le_mul_of_nonneg_right _ hlog
    have h3 : ((n / p : ℕ) : ℝ) ≤ ((n.factorial).factorization p : ℝ) := by
      exact_mod_cast div_le_factorization_factorial hpp n
    have h4 : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by
      exact_mod_cast Nat.lt_div_mul_add hpp.pos
    have h5 : (n : ℝ) / p < ((n / p : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hp0]; linarith
    linarith
  have h6 : ∑ p ∈ Nat.primesLE n, ((n : ℝ) / p - 1) * Real.log p =
      n * ∑ p ∈ Nat.primesLE n, Real.log p / p - ∑ p ∈ Nat.primesLE n, Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have h7 : ∑ p ∈ Nat.primesLE n, Real.log p ≤ Real.log 4 * n := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have h8 : n * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ n * (Real.log n + Real.log 4) := by
    linarith
  exact le_of_mul_le_mul_left h8 hn0

private lemma mertens_log_succ_le (x : ℝ) (hx : 0 < x) : Real.log (x + 1) ≤ Real.log x + 1 / x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  rw [Real.log_div (by positivity) hx.ne'] at h
  have h' : (x + 1) / x - 1 = 1 / x := by field_simp; ring
  linarith

private lemma mertens_tail_step (x : ℝ) (hx : 1 < x) :
    Real.log x / (x * (x - 1)) + (Real.log (x + 1) + 1) / x ≤ (Real.log x + 1) / (x - 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have h1 : Real.log (x + 1) - Real.log x ≤ 1 / x := by linarith [mertens_log_succ_le x hx0]
  have h2 : (x - 1) * (Real.log (x + 1) - Real.log x) ≤ (x - 1) * (1 / x) :=
    mul_le_mul_of_nonneg_left h1 hx1.le
  have h3 : (x - 1) * (1 / x) ≤ 1 := by rw [mul_one_div, div_le_one hx0]; linarith
  have key : (Real.log x + 1) / (x - 1) - Real.log x / (x * (x - 1)) -
      (Real.log (x + 1) + 1) / x =
      (1 - (x - 1) * (Real.log (x + 1) - Real.log x)) / (x * (x - 1)) := by
    field_simp; ring
  have h4 : 0 ≤ (1 - (x - 1) * (Real.log (x + 1) - Real.log x)) / (x * (x - 1)) :=
    div_nonneg (by linarith) (by positivity)
  linarith

private lemma mertens_tail_bound (n : ℕ) :
    ∑ m ∈ Finset.Icc 2 (n + 1), Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) +
      (Real.log ((n : ℝ) + 2) + 1) / ((n : ℝ) + 1) ≤ Real.log 2 + 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h := mertens_tail_step ((k : ℝ) + 2) (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have e0 : ((k + 1 + 1 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    have e1 : (k : ℝ) + 2 - 1 = k + 1 := by ring
    have e2 : ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 2 + 1 := by push_cast; ring
    have e3 : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    rw [e0, e2, e3]; rw [e1] at h ⊢; linarith

private lemma mertens_first_lower (n : ℕ) (hn : 1 ≤ n) :
    Real.log n - (2 + Real.log 2) ≤ ∑ p ∈ Nat.primesLE n, Real.log p / p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := stirling_lower n hn
  have h2 : Real.log (n.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE n, (n : ℝ) / ((p : ℝ) - 1) * Real.log p := by
    rw [log_factorial_eq_sum_primesLE]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    apply mul_le_mul_of_nonneg_right _ hlog
    have h3 : ((n.factorial).factorization p : ℝ) ≤ ((n / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp n
    have h4 : ((n / (p - 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    rw [Nat.cast_sub hpp.one_le, Nat.cast_one] at h4
    linarith
  have h5 : ∑ p ∈ Nat.primesLE n, (n : ℝ) / ((p : ℝ) - 1) * Real.log p =
      n * ∑ p ∈ Nat.primesLE n, Real.log p / p +
        n * ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      linarith
    field_simp; ring
  have h6 : ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ Real.log 2 + 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hsub : Nat.primesLE (k + 1) ⊆ Finset.Icc 2 (k + 1) := by
      rw [Nat.primesLE_eq_filter_Icc_two]; exact Finset.filter_subset _ _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun m : ℕ => Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1))) (fun m hm _ => by
        rw [Finset.mem_Icc] at hm
        have h2m : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
        exact div_nonneg (Real.log_nonneg (by linarith)) (mul_nonneg (by linarith) (by linarith)))
    have hb := mertens_tail_bound k
    have hpos : 0 ≤ (Real.log ((k : ℝ) + 2) + 1) / ((k : ℝ) + 1) :=
      div_nonneg (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ (k : ℝ) + 2 by linarith)])
        (by positivity)
    linarith
  have h7 : n * (Real.log n - (2 + Real.log 2)) ≤ n * ∑ p ∈ Nat.primesLE n, Real.log p / p := by
    have := mul_le_mul_of_nonneg_left h6 hn0.le
    nlinarith
  exact le_of_mul_le_mul_left h7 hn0

private lemma mertens_first_explicit (n : ℕ) (hn : 1 ≤ n) :
    |∑ p ∈ Nat.primesLE n, Real.log p / p - Real.log n| ≤ 2 + Real.log 2 := by
  rw [abs_le]
  have h1 := mertens_first_upper n hn
  have h2 := mertens_first_lower n hn
  have h3 : Real.log 4 ≤ 2 + Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num; linarith [Real.log_two_lt_d9]
  constructor <;> linarith

private lemma primesLE_sum_succ (f : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ Nat.primesLE (n + 1), f p =
      ∑ p ∈ Nat.primesLE n, f p + if (n + 1).Prime then f (n + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert (Nat.notMem_primesLE n)]; ring
  · simp

private lemma mertens_sum_by_parts (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ Nat.primesLE n, (1 : ℝ) / p =
      (∑ p ∈ Nat.primesLE n, Real.log p / p) * (1 / Real.log (n : ℝ)) +
        ∑ m ∈ Finset.Ico 2 n, (∑ p ∈ Nat.primesLE m, Real.log p / p) *
          (1 / Real.log (m : ℝ) - 1 / Real.log ((m + 1 : ℕ) : ℝ)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h2 : Nat.primesLE 2 = {2} := by decide
    have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    simp [h2]; field_simp
  | succ n hn ih =>
    rw [primesLE_sum_succ, primesLE_sum_succ, Finset.sum_Ico_succ_top hn, ih]
    have hx : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hl : Real.log ((n + 1 : ℕ) : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))).ne'
    split_ifs with hp
    · have e : (∑ p ∈ Nat.primesLE n, Real.log p / p +
            Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) * (1 / Real.log ((n + 1 : ℕ) : ℝ)) =
          (∑ p ∈ Nat.primesLE n, Real.log p / p) * (1 / Real.log ((n + 1 : ℕ) : ℝ)) +
            1 / ((n + 1 : ℕ) : ℝ) := by field_simp
      rw [e]; ring
    · ring

private lemma mertens_loglog_step (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ u + 1 / 2) :
    u * (1 / u - 1 / v) ≤ Real.log v - Real.log u ∧
      Real.log v - Real.log u ≤ (u + 1 / 2) * (1 / u - 1 / v) := by
  have hv0 : 0 < v := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < v / u by positivity)
  have h2 := Real.log_le_sub_one_of_pos (show 0 < v / u by positivity)
  rw [Real.log_div hv0.ne' hu.ne'] at h1 h2
  constructor
  · have e : u * (1 / u - 1 / v) = 1 - (v / u)⁻¹ := by field_simp
    linarith
  · have e : (u + 1 / 2) * (1 / u - 1 / v) - (v / u - 1) =
        (v - u) * (u + 1 / 2 - v) / (u * v) := by field_simp
    have h3 : 0 ≤ (v - u) * (u + 1 / 2 - v) / (u * v) :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
    linarith

private noncomputable def primeLogWeight (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, Real.log p / p

private noncomputable def logStep (n : ℕ) : ℝ :=
  1 / Real.log (n + 2 : ℕ) - 1 / Real.log (n + 1 + 2 : ℕ)

private lemma logStep_nonneg (n : ℕ) : 0 ≤ logStep n := by
  unfold logStep
  apply sub_nonneg.mpr
  refine one_div_le_one_div_of_le (Real.log_pos (by norm_cast; omega)) ?_
  exact Real.log_le_log (by positivity) (by norm_cast; omega)

private lemma summable_logStep : Summable logStep := by
  refine summable_of_sum_range_le logStep_nonneg (c := 1 / Real.log 2) fun n => ?_
  simp only [logStep]
  rw [Finset.sum_range_sub']
  have h : 0 ≤ 1 / Real.log (n + 2 : ℕ) :=
    div_nonneg zero_le_one (Real.log_natCast_nonneg _)
  simp only [zero_add, Nat.cast_ofNat]
  linarith

private noncomputable def mertensIncrement (n : ℕ) : ℝ :=
  primeLogWeight (n + 2) * logStep n -
    (Real.log (Real.log (n + 1 + 2 : ℕ)) - Real.log (Real.log (n + 2 : ℕ)))

private lemma norm_mertensIncrement_le (n : ℕ) :
    ‖mertensIncrement n‖ ≤ (2 + Real.log 2 + 1 / 2) * logStep n := by
  let k := n + 2
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by dsimp [k]; omega)
  let u := Real.log (k : ℝ)
  let v := Real.log ((k + 1 : ℕ) : ℝ)
  have hu : 0 < u := Real.log_pos (by linarith)
  have huv : u ≤ v := Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ k)
  have hv : v ≤ u + 1 / 2 := by
    dsimp [u, v]
    push_cast
    have h1 := mertens_log_succ_le (k : ℝ) (by linarith)
    have h2 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hk
    linarith
  have hw : 1 / u - 1 / v = logStep n := by
    have h : n + 1 + 2 = k + 1 := rfl
    simp [logStep, u, v, k, h]
  obtain ⟨hlo, hhi⟩ := mertens_loglog_step u v hu huv hv
  rw [hw] at hlo hhi
  have hs : |primeLogWeight k - u| ≤ 2 + Real.log 2 :=
    mertens_first_explicit k (by dsimp [k]; omega)
  rw [abs_le] at hs
  have hsw1 := mul_le_mul_of_nonneg_right hs.1 (logStep_nonneg n)
  have hsw2 := mul_le_mul_of_nonneg_right hs.2 (logStep_nonneg n)
  have hstep : n + 1 + 2 = k + 1 := rfl
  unfold mertensIncrement
  rw [hstep, Real.norm_eq_abs, abs_le]
  change -((2 + Real.log 2 + 1 / 2) * logStep n) ≤
      primeLogWeight k * logStep n - (Real.log v - Real.log u) ∧ _
  constructor <;> linarith

private lemma tendsto_primeLogWeight_div :
    Tendsto (fun n : ℕ => primeLogWeight n / Real.log n) atTop (𝓝 1) := by
  let C := 2 + Real.log 2
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hC : Tendsto (fun n : ℕ => C / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hl : Tendsto (fun n : ℕ => 1 - C / Real.log n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hC
  have hh : Tendsto (fun n : ℕ => 1 + C / Real.log n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hC
  apply hl.squeeze' hh
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have h : |primeLogWeight n - Real.log n| ≤ C := mertens_first_explicit n (by omega)
    rw [abs_le] at h
    rw [le_div_iff₀ hpos, sub_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
    linarith [h.1]
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have h : |primeLogWeight n - Real.log n| ≤ C := mertens_first_explicit n (by omega)
    rw [abs_le] at h
    rw [div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
    linarith [h.2]

private lemma exists_prime_reciprocal_limit :
    ∃ B : ℝ, Tendsto (fun n : ℕ => (∑ p ∈ n.primesLE, (1 : ℝ) / p) -
      Real.log (Real.log n)) atTop (𝓝 B) := by
  have hs : Summable mertensIncrement :=
    (summable_logStep.mul_left (2 + Real.log 2 + 1 / 2)).of_norm_bounded norm_mertensIncrement_le
  let B := 1 - Real.log (Real.log 2) + ∑' k, mertensIncrement k
  refine ⟨B, (tendsto_add_atTop_iff_nat 2).mp ?_⟩
  have hf (n : ℕ) :
      (∑ p ∈ (n + 2).primesLE, (1 : ℝ) / p) - Real.log (Real.log (n + 2 : ℕ)) =
        (primeLogWeight (n + 2) / Real.log (n + 2 : ℕ) - Real.log (Real.log 2)) +
          ∑ k ∈ Finset.range n, mertensIncrement k := by
    rw [mertens_sum_by_parts _ (by omega), Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, mertensIncrement]
    rw [Finset.sum_sub_distrib]
    have hn : (∑ k ∈ Finset.range n, (Real.log (Real.log (k + 1 + 2 : ℕ)) -
        Real.log (Real.log (k + 2 : ℕ)))) =
        Real.log (Real.log (n + 2 : ℕ)) - Real.log (Real.log 2) := by
      rw [Finset.sum_range_sub (fun k : ℕ => Real.log (Real.log (k + 2 : ℕ))) n]
      rfl
    rw [hn]
    have heq (k : ℕ) : k + 2 + 1 = k + 1 + 2 := by omega
    simp only [primeLogWeight, logStep, Nat.add_comm 2, heq, div_eq_mul_inv, one_mul]
    ring
  simp_rw [hf]
  have h := (tendsto_add_atTop_iff_nat 2).mpr tendsto_primeLogWeight_div
  exact (h.sub tendsto_const_nhds).add hs.hasSum.tendsto_sum_nat

private lemma neg_log_one_sub_sub_bounds {u : ℝ} (hu' : u ≤ 1 / 2) :
    0 ≤ -Real.log (1 - u) - u ∧ -Real.log (1 - u) - u ≤ 2 * u ^ 2 := by
  have hpos : 0 < 1 - u := by linarith
  have hl := Real.log_le_sub_one_of_pos hpos
  have hh := Real.one_sub_inv_le_log_of_pos hpos
  have hf : (1 - u)⁻¹ - 1 - u = u ^ 2 / (1 - u) := by field_simp; ring
  have hq : u ^ 2 / (1 - u) ≤ 2 * u ^ 2 := by
    rw [div_le_iff₀ hpos]
    have hmul := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * (1 - u) by linarith) (sq_nonneg u)
    linarith
  exact ⟨by linarith, by linarith⟩

private noncomputable def primeLogCorrection (n : ℕ) : ℝ :=
  if n.Prime then -Real.log (1 - 1 / (n : ℝ)) - 1 / n else 0

private lemma summable_primeLogCorrection : Summable primeLogCorrection := by
  have hbase := (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2 : ℕ))).mul_left (2 : ℝ)
  refine hbase.of_norm_bounded fun n => ?_
  unfold primeLogCorrection
  split_ifs with hn
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
    have hhalf : (1 : ℝ) / n ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2
    obtain ⟨hlo, hhi⟩ := neg_log_one_sub_sub_bounds hhalf
    simp only [Real.norm_eq_abs, abs_of_nonneg hlo]
    simpa [one_div, inv_pow] using hhi
  · simp

private lemma exists_prime_log_product_limit :
    ∃ B : ℝ, Tendsto (fun n : ℕ =>
      (∑ p ∈ n.primesLE, -Real.log (1 - 1 / (p : ℝ))) - Real.log (Real.log n))
      atTop (𝓝 B) := by
  obtain ⟨b, hb⟩ := exists_prime_reciprocal_limit
  have hc := summable_primeLogCorrection.hasSum.tendsto_sum_nat
  refine ⟨b + ∑' n, primeLogCorrection n, ?_⟩
  have hcc := (tendsto_add_atTop_iff_nat 1).mpr hc
  refine (hb.add hcc).congr fun n => ?_
  rw [show (∑ i ∈ Finset.range (n + 1), primeLogCorrection i) =
      ∑ p ∈ n.primesLE, (-Real.log (1 - 1 / (p : ℝ)) - 1 / p) by
    simp only [primeLogCorrection, Nat.primesLE, Nat.primesBelow, Finset.sum_filter]]
  rw [Finset.sum_sub_distrib]
  ring

private lemma prime_prod_sdiff_tendsto (u v : ℕ → ℕ)
    (hu : Tendsto u atTop atTop) (huv : ∀ᶠ x in atTop, u x ≤ v x) :
    Tendsto (fun x =>
      (∏ p ∈ (v x).primesLE \ (u x).primesLE, (1 - 1 / (p : ℝ))) *
        (Real.log (v x : ℝ) / Real.log (u x : ℝ))) atTop (𝓝 1) := by
  obtain ⟨B, hB⟩ := exists_prime_log_product_limit
  have hv : Tendsto v atTop atTop := tendsto_atTop_mono' atTop huv hu
  have hdiff : Tendsto (fun x =>
      ((∑ p ∈ (v x).primesLE, -Real.log (1 - 1 / (p : ℝ))) - Real.log (Real.log (v x : ℝ))) -
      ((∑ p ∈ (u x).primesLE, -Real.log (1 - 1 / (p : ℝ))) - Real.log (Real.log (u x : ℝ))))
      atTop (𝓝 0) := by
    simpa using (hB.comp hv).sub (hB.comp hu)
  have hdiff_neg : Tendsto (fun x => -(((∑ p ∈ (v x).primesLE, -Real.log (1 - 1 / (p : ℝ))) -
      Real.log (Real.log (v x : ℝ))) -
      ((∑ p ∈ (u x).primesLE, -Real.log (1 - 1 / (p : ℝ))) - Real.log (Real.log (u x : ℝ)))))
      atTop (𝓝 0) := by
    simpa only [neg_zero] using hdiff.neg
  have hexp : Tendsto (fun x => Real.exp (-(((∑ p ∈ (v x).primesLE, -Real.log (1 - 1 / (p : ℝ))) -
      Real.log (Real.log (v x : ℝ))) -
      ((∑ p ∈ (u x).primesLE, -Real.log (1 - 1 / (p : ℝ))) - Real.log (Real.log (u x : ℝ))))))
      atTop (𝓝 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp hdiff_neg
    rw [Real.exp_zero] at h
    exact h
  refine hexp.congr' ?_
  filter_upwards [huv, hu.eventually_ge_atTop 2] with x hle hu2
  have hv2 : 2 ≤ v x := hu2.trans hle
  have hlu : 0 < Real.log (u x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < u x by omega))
  have hlv : 0 < Real.log (v x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < v x by omega))
  have hsum :
      (∑ p ∈ (v x).primesLE, -Real.log (1 - 1 / (p : ℝ))) -
      (∑ p ∈ (u x).primesLE, -Real.log (1 - 1 / (p : ℝ))) =
      ∑ p ∈ (v x).primesLE \ (u x).primesLE, -Real.log (1 - 1 / (p : ℝ)) :=
    (Finset.sum_sdiff_eq_sub (Nat.primesLE_mono hle)).symm
  have harg : -(((∑ p ∈ (v x).primesLE, -Real.log (1 - 1 / (p : ℝ))) -
      Real.log (Real.log (v x : ℝ))) -
      ((∑ p ∈ (u x).primesLE, -Real.log (1 - 1 / (p : ℝ))) - Real.log (Real.log (u x : ℝ)))) =
      (∑ p ∈ (v x).primesLE \ (u x).primesLE, Real.log (1 - 1 / (p : ℝ))) +
        (Real.log (Real.log (v x : ℝ)) - Real.log (Real.log (u x : ℝ))) := by
    have hneg : ∑ p ∈ (v x).primesLE \ (u x).primesLE, -Real.log (1 - 1 / (p : ℝ)) =
        -(∑ p ∈ (v x).primesLE \ (u x).primesLE, Real.log (1 - 1 / (p : ℝ))) := by
      rw [Finset.sum_neg_distrib]
    linarith
  rw [harg, Real.exp_add, Real.exp_sum, Real.exp_sub, Real.exp_log hlv, Real.exp_log hlu]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hpos : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  exact Real.exp_log hpos

private lemma tendsto_log_natFloor_div_log {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    Tendsto (fun x => Real.log (⌊f x⌋₊ : ℝ) / Real.log (f x)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun x => Real.log (f x)) atTop atTop := Real.tendsto_log_atTop.comp hf
  have hlo : Tendsto (fun x => 1 - Real.log 2 / Real.log (f x)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hlog)
  apply hlo.squeeze' tendsto_const_nhds
  · filter_upwards [hf.eventually_ge_atTop 2] with x hx
    have hfl_gt : f x / 2 ≤ (⌊f x⌋₊ : ℝ) := by linarith [Nat.sub_one_lt_floor (f x)]
    have hlpos : 0 < Real.log (f x) := Real.log_pos (by linarith)
    have hlg := Real.log_le_log (by positivity) hfl_gt
    rw [Real.log_div (by positivity) (by norm_num)] at hlg
    rw [le_div_iff₀ hlpos, sub_mul, div_mul_cancel₀ _ hlpos.ne', one_mul]
    linarith
  · filter_upwards [hf.eventually_ge_atTop 2] with x hx
    have hlpos : 0 < Real.log (f x) := Real.log_pos (by linarith)
    have hfl_pos : 0 < (⌊f x⌋₊ : ℝ) := by linarith [Nat.sub_one_lt_floor (f x)]
    rw [div_le_one hlpos]
    exact Real.log_le_log hfl_pos (Nat.floor_le (by linarith))

private lemma tendsto_log_div_id :
    Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

private lemma tendsto_log_sq_div_id :
    Tendsto (fun t : ℝ => (Real.log t) ^ 2 / t) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.rpow_two, Real.rpow_one]

private lemma tendsto_id_div_log :
    Tendsto (fun t : ℝ => t / Real.log t) atTop atTop := by
  have hgt : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_log_div_id, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact div_pos (Real.log_pos ht) (by linarith)
  have hinv := hgt.inv_tendsto_nhdsGT_zero
  refine hinv.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t _
  simp only [Pi.inv_apply, inv_div]

private lemma main_sieve_bound (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      let X : ℝ := x
      let U := Real.log (Real.log X)
      let y := c * X * Real.log X * Real.log U / U
      let z := X ^ (Real.log U / (4 * U))
      let P := (Finset.Ioc (x / 2) x).filter Nat.Prime
      let S := (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ p ∉ P ∧ Real.log X ^ 20 < p)
      let V := (Finset.Ioc x ⌊y⌋₊).filter Nat.Prime
      let M := (V.card : ℝ) * (∏ p ∈ S, (1 - 1 / (p : ℝ)))
      0 < ⌊y⌋₊ ∧ 1 < Real.log X ^ 20 ∧
        Real.exp ((Real.log ⌊y⌋₊ / Real.log 2) / (Real.log X ^ 20 - 1)) ≤ 1 + 1 / 128 ∧
        128 ≤ M ∧ 60 * c * (X * U / Real.log X) ≤ M ∧ M ≤ 100 * c * (X * U / Real.log X) := by
  let X : ℕ → ℝ := fun x => (x : ℝ)
  let L : ℕ → ℝ := fun x => Real.log (X x)
  let U : ℕ → ℝ := fun x => Real.log (L x)
  let y : ℕ → ℝ := fun x => c * X x * L x * Real.log (U x) / U x
  let z : ℕ → ℝ := fun x => (X x) ^ (Real.log (U x) / (4 * U x))
  let u : ℕ → ℕ := fun x => ⌊(L x) ^ 20⌋₊
  let v : ℕ → ℕ := fun x => ⌊z x⌋₊
  have hX : Tendsto X atTop atTop := tendsto_natCast_atTop_atTop
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp hX
  have hU : Tendsto U atTop atTop := Real.tendsto_log_atTop.comp hL
  have hlogU : Tendsto (fun x => Real.log (U x)) atTop atTop := Real.tendsto_log_atTop.comp hU
  have hlogU_div_U : Tendsto (fun x => Real.log (U x) / U x) atTop (𝓝 0) :=
    tendsto_log_div_id.comp hU
  have hU_div_L : Tendsto (fun x => U x / L x) atTop (𝓝 0) :=
    tendsto_log_div_id.comp hL
  have hU2_div_L : Tendsto (fun x => (U x) ^ 2 / L x) atTop (𝓝 0) :=
    tendsto_log_sq_div_id.comp hL
  have hL_div_U : Tendsto (fun x => L x / U x) atTop atTop :=
    tendsto_id_div_log.comp hL
  have hX_div_L : Tendsto (fun x => X x / L x) atTop atTop :=
    tendsto_id_div_log.comp hX
  have hXU_div_L : Tendsto (fun x => X x * U x / L x) atTop atTop := by
    have h := hX_div_L.atTop_mul_atTop₀ hU
    refine h.congr fun x => by ring
  have hy_div_X : Tendsto (fun x => y x / X x) atTop atTop := by
    have h1 := (hL_div_U.atTop_mul_atTop₀ hlogU).const_mul_atTop hc
    refine h1.congr' ?_
    filter_upwards [hX.eventually_gt_atTop 0] with x hx
    dsimp only [y]
    field_simp [hx.ne']
  have hy_top : Tendsto y atTop atTop := by
    have h := hy_div_X.atTop_mul_atTop₀ hX
    refine h.congr' ?_
    filter_upwards [hX.eventually_gt_atTop 0] with x hx
    field_simp [hx.ne']
  have hlogy_div_L : Tendsto (fun x => Real.log (y x) / L x) atTop (𝓝 1) := by
    have h1 : Tendsto (fun x => Real.log c / L x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hL
    have h2 : Tendsto (fun x => Real.log (U x) / L x) atTop (𝓝 0) := by
      have h := hlogU_div_U.mul hU_div_L
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [hU.eventually_gt_atTop 0] with x hx
      field_simp [hx.ne']
    have h3 : Tendsto (fun x => Real.log (Real.log (U x)) / L x) atTop (𝓝 0) := by
      have h := (tendsto_log_div_id.comp hlogU).mul h2
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [hlogU.eventually_gt_atTop 0] with x hx
      dsimp only [Function.comp_apply]
      field_simp [hx.ne']
    have hsum : Tendsto (fun x => 1 + Real.log c / L x + U x / L x +
        Real.log (Real.log (U x)) / L x - Real.log (U x) / L x) atTop (𝓝 1) := by
      simpa using ((((tendsto_const_nhds.add h1).add hU_div_L).add h3).sub h2)
    refine hsum.congr' ?_
    filter_upwards [hX.eventually_gt_atTop 0, hL.eventually_gt_atTop 0,
      hU.eventually_gt_atTop 0, hlogU.eventually_gt_atTop 0] with x hXp hLp hUp hlogUp
    dsimp only [y]
    have hnum : c * X x * L x * Real.log (U x) ≠ 0 := by positivity
    rw [Real.log_div hnum hUp.ne',
      Real.log_mul (by positivity) hlogUp.ne',
      Real.log_mul (by positivity) hLp.ne',
      Real.log_mul hc.ne' hXp.ne']
    change 1 + Real.log c / L x + U x / L x + Real.log (Real.log (U x)) / L x -
        Real.log (U x) / L x =
      (Real.log c + L x + U x + Real.log (Real.log (U x)) - Real.log (U x)) / L x
    field_simp [hLp.ne']
    ring
  have hlogz_eq : ∀ᶠ x in atTop, Real.log (z x) = (Real.log (U x) / (4 * U x)) * L x := by
    filter_upwards [hX.eventually_gt_atTop 0] with x hx
    dsimp only [z, L]
    rw [Real.log_rpow hx, mul_comm]
  have hlogz_top : Tendsto (fun x => Real.log (z x)) atTop atTop := by
    have h1 : Tendsto (fun x => (Real.log (U x) / 4) * (L x / U x)) atTop atTop :=
      (hlogU.atTop_div_const (by norm_num : (0 : ℝ) < 4)).atTop_mul_atTop₀ hL_div_U
    refine h1.congr' ?_
    filter_upwards [hlogz_eq] with x hx
    rw [hx]; ring
  have hz_top : Tendsto z atTop atTop := by
    have h := Real.tendsto_exp_atTop.comp hlogz_top
    refine h.congr' ?_
    filter_upwards [hX.eventually_gt_atTop 0] with x hx
    exact Real.exp_log (Real.rpow_pos_of_pos hx _)
  have hL20_top : Tendsto (fun x => (L x) ^ 20) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 20 ≠ 0)).comp hL
  have hu_top : Tendsto u atTop atTop := tendsto_nat_floor_atTop.comp hL20_top
  have huv_ev : ∀ᶠ x in atTop, u x ≤ v x := by
    have hratio : Tendsto (fun x => (80 : ℝ) * ((U x) ^ 2 / L x)) atTop (𝓝 0) := by
      simpa using hU2_div_L.const_mul (80 : ℝ)
    filter_upwards [hL.eventually_ge_atTop 2, hU.eventually_ge_atTop 1,
      hlogU.eventually_ge_atTop 1, hlogz_eq,
      hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hX.eventually_gt_atTop 0] with x hL2 hU1 hlogU1 hlz hrat hXp
    apply Nat.floor_mono
    have hlt_log : Real.log ((L x) ^ 20) < Real.log (z x) := by
      rw [Real.log_pow, hlz]
      change 20 * U x < (Real.log (U x) / (4 * U x)) * L x
      have h1 : 80 * (U x) ^ 2 < L x := by
        have h3 : (80 * (U x) ^ 2) / L x < 1 := by
          rw [mul_div_assoc]; exact hrat
        exact (div_lt_one (by linarith : 0 < L x)).mp h3
      have h4 : 80 * (U x) ^ 2 < L x * Real.log (U x) := by nlinarith
      rw [div_mul_eq_mul_div, lt_div_iff₀ (by linarith : 0 < 4 * U x)]
      nlinarith
    have hpos1 : 0 < (L x) ^ 20 := by positivity
    have hpos2 : 0 < z x := Real.rpow_pos_of_pos hXp _
    exact (Real.log_lt_log_iff hpos1 hpos2).mp hlt_log |>.le
  have hv_le_half : ∀ᶠ x in atTop, v x ≤ x / 2 := by
    filter_upwards [hX.eventually_ge_atTop 16, hU.eventually_gt_atTop 0,
      hlogU_div_U.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2))] with x hx16 hUp hrat
    have hexp_le : Real.log (U x) / (4 * U x) ≤ 1 / 2 := by
      have : Real.log (U x) / (4 * U x) = (Real.log (U x) / U x) / 4 := by ring
      linarith
    have hz_le_sqrt : z x ≤ Real.sqrt (X x) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ X x) hexp_le
    have hsqrt_le : Real.sqrt (X x) ≤ X x / 4 := by
      have hsq : X x ≤ (X x / 4) ^ 2 := by nlinarith
      exact (Real.sqrt_le_left (by linarith)).mpr hsq
    have hz_le : z x ≤ (x / 2 : ℕ) := by
      have hdiv : (X x - 1) / 2 ≤ (x / 2 : ℕ) := by
        have hnat : x ≤ 2 * (x / 2) + 1 := by omega
        have hreal : (x : ℝ) ≤ 2 * ((x / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
        dsimp only [X]
        linarith
      linarith
    exact Nat.floor_le_of_le hz_le
  have hS_eq : ∀ᶠ x in atTop,
      (Finset.range (⌊z x⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ p ∉ (Finset.Ioc (x / 2) x).filter Nat.Prime ∧ (L x) ^ 20 < p) =
      (v x).primesLE \ (u x).primesLE := by
    filter_upwards [hv_le_half, hL.eventually_ge_atTop 0] with x hvh hL0
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff, Nat.mem_primesLE,
      Finset.mem_Ioc, Nat.lt_succ_iff]
    have hfloor : (L x) ^ 20 < (p : ℝ) ↔ u x < p :=
      (Nat.floor_lt (pow_nonneg hL0 20)).symm
    constructor
    · rintro ⟨hpv, hpp, _, hpu⟩
      have hpu' : u x < p := hfloor.mp hpu
      exact ⟨⟨hpv, hpp⟩, fun h => by omega⟩
    · rintro ⟨⟨hpv, hpp⟩, hnot⟩
      have hpu' : u x < p := by
        by_contra hle
        exact hnot ⟨by omega, hpp⟩
      refine ⟨hpv, hpp, ?_, hfloor.mpr hpu'⟩
      rintro ⟨⟨hgt, _⟩, _⟩
      omega
  have hlogu_lim : Tendsto (fun x => Real.log (u x : ℝ) / (20 * U x)) atTop (𝓝 1) := by
    have h := tendsto_log_natFloor_div_log hL20_top
    refine h.congr' ?_
    filter_upwards [hL.eventually_gt_atTop 0] with x hLp
    rw [Real.log_pow]
    rfl
  have hlogv_lim :
      Tendsto (fun x => Real.log (v x : ℝ) / ((Real.log (U x) / (4 * U x)) * L x)) atTop (𝓝 1) := by
    have h := tendsto_log_natFloor_div_log hz_top
    refine h.congr' ?_
    filter_upwards [hlogz_eq] with x hx
    rw [hx]
  have hprod_lim :
      Tendsto (fun x => (∏ p ∈ (v x).primesLE \ (u x).primesLE, (1 - 1 / (p : ℝ))) *
        (L x * Real.log (U x) / (80 * (U x) ^ 2))) atTop (𝓝 1) := by
    have hmert := prime_prod_sdiff_tendsto u v hu_top huv_ev
    have hcomb := (hmert.mul hlogu_lim).div hlogv_lim (by norm_num : (1 : ℝ) ≠ 0)
    simp only [mul_one, div_one] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [hu_top.eventually_ge_atTop 2, huv_ev, hL.eventually_gt_atTop 0,
      hU.eventually_gt_atTop 0, hlogU.eventually_gt_atTop 0] with x hu2 huv hLp hUp hlogUp
    have hv2 : 2 ≤ v x := hu2.trans huv
    have hlu : Real.log (u x : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < u x by omega))).ne'
    have hlv : Real.log (v x : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < v x by omega))).ne'
    dsimp only [Pi.div_apply]
    field_simp [hlu, hlv, hLp.ne', hUp.ne', hlogUp.ne']
    ring
  have hV_bounds : ∀ᶠ x in atTop,
      (85 / 100 : ℝ) * (c * X x * Real.log (U x) / U x) ≤
        (((Finset.Ioc x ⌊y x⌋₊).filter Nat.Prime).card : ℝ) ∧
      (((Finset.Ioc x ⌊y x⌋₊).filter Nat.Prime).card : ℝ) ≤
        (115 / 100 : ℝ) * (c * X x * Real.log (U x) / U x) := by
    have hpi_y := hy_top.eventually eventually_primeCounting_cheb_bounds
    have hpi_x := hX.eventually eventually_primeCounting_cheb_bounds
    have hsmall : Tendsto (fun x => (X x / L x) / (y x / Real.log (y x))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x => (y x / X x)⁻¹ * (Real.log (y x) / L x)) atTop (𝓝 0) := by
        simpa using (tendsto_inv_atTop_zero.comp hy_div_X).mul hlogy_div_L
      refine h1.congr' ?_
      filter_upwards [hX.eventually_gt_atTop 0, hL.eventually_gt_atTop 0,
        hy_top.eventually_gt_atTop 2] with x hXp hLp hy2
      have hly : Real.log (y x) ≠ 0 := (Real.log_pos (by linarith)).ne'
      field_simp [hXp.ne', hLp.ne', (show y x ≠ 0 by linarith), hly]
    filter_upwards [hpi_y, hpi_x,
      hsmall.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 11300 by norm_num)),
      hlogy_div_L.eventually (Ioo_mem_nhds (by norm_num : (99 / 100 : ℝ) < 1)
        (by norm_num : (1 : ℝ) < 101 / 100)),
      hy_div_X.eventually_ge_atTop 2, hX.eventually_ge_atTop 2,
      hL.eventually_gt_atTop 0, hU.eventually_gt_atTop 0, hlogU.eventually_gt_atTop 0]
      with x ⟨hpy_lo, hpy_hi⟩ ⟨_, hpx_hi⟩ hsm ⟨hlr_lo, hlr_hi⟩ hyx hX2 hLp hUp hlogUp
    have hy_ge : X x + 1 ≤ y x := by
      have h1 : 2 * X x ≤ y x := (le_div_iff₀ (by linarith : 0 < X x)).mp hyx
      linarith
    have hx_le_fy : x ≤ ⌊y x⌋₊ := Nat.le_floor (by linarith)
    have hV_eq : (Finset.Ioc x ⌊y x⌋₊).filter Nat.Prime = ⌊y x⌋₊.primesLE \ x.primesLE := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨⟨h2, hp⟩, fun h => by omega⟩
      · rintro ⟨⟨h2, hp⟩, hnot⟩
        refine ⟨⟨?_, h2⟩, hp⟩
        by_contra hle; exact hnot ⟨by omega, hp⟩
    have hcard_eq : (((Finset.Ioc x ⌊y x⌋₊).filter Nat.Prime).card : ℝ) =
        (Nat.primeCounting ⌊y x⌋₊ : ℝ) - (Nat.primeCounting x : ℝ) := by
      rw [hV_eq, Finset.card_sdiff, Finset.inter_eq_left.mpr (Nat.primesLE_mono hx_le_fy),
        Nat.cast_sub (Finset.card_le_card (Nat.primesLE_mono hx_le_fy)),
        Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
    rw [hcard_eq]
    have hfx : ⌊X x⌋₊ = x := Nat.floor_natCast x
    rw [hfx] at hpx_hi
    have hy_pos : 0 < y x := by linarith
    have hly_pos : 0 < Real.log (y x) := Real.log_pos (by linarith)
    have hyl_pos : 0 < y x / Real.log (y x) := div_pos hy_pos hly_pos
    have hpx_small : (Nat.primeCounting x : ℝ) ≤ (1 / 100 : ℝ) * (y x / Real.log (y x)) := by
      have h1 : X x / L x < (1 / 11300 : ℝ) * (y x / Real.log (y x)) :=
        (div_lt_iff₀ hyl_pos).mp hsm
      linarith
    have hy_div_L : y x / L x = c * X x * Real.log (U x) / U x := by
      dsimp only [y]
      field_simp [hLp.ne', hUp.ne']
    have hly_lo : (99 / 100 : ℝ) * L x ≤ Real.log (y x) :=
      (le_div_iff₀ hLp).mp hlr_lo.le
    have hly_hi : Real.log (y x) ≤ (101 / 100 : ℝ) * L x :=
      (div_le_iff₀ hLp).mp hlr_hi.le
    have hbase_nn : 0 ≤ y x / L x := div_nonneg hy_pos.le hLp.le
    have hyl_lo : (100 / 101 : ℝ) * (y x / L x) ≤ y x / Real.log (y x) := by
      rw [le_div_iff₀ hly_pos]
      have hmul := mul_le_mul_of_nonneg_left hly_hi hbase_nn
      have e : y x / L x * ((101 / 100 : ℝ) * L x) = (101 / 100 : ℝ) * y x := by
        field_simp [hLp.ne']
      linarith
    have hyl_hi : y x / Real.log (y x) ≤ (100 / 99 : ℝ) * (y x / L x) := by
      rw [div_le_iff₀ hly_pos]
      have hmul := mul_le_mul_of_nonneg_left hly_lo hbase_nn
      have e : y x / L x * ((99 / 100 : ℝ) * L x) = (99 / 100 : ℝ) * y x := by
        field_simp [hLp.ne']
      linarith
    have hpx_nn : (0 : ℝ) ≤ Nat.primeCounting x := Nat.cast_nonneg _
    rw [← hy_div_L]
    constructor <;> linarith
  have hexp_lim :
      Tendsto (fun x => Real.exp ((Real.log (⌊y x⌋₊ : ℝ) / Real.log 2) / ((L x) ^ 20 - 1)))
        atTop (𝓝 1) := by
    have harg : Tendsto (fun x => (Real.log (⌊y x⌋₊ : ℝ) / Real.log 2) / ((L x) ^ 20 - 1))
        atTop (𝓝 0) := by
      have hhi : Tendsto (fun x => (2 / Real.log 2) / L x) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hL
      apply tendsto_const_nhds.squeeze' hhi
      · filter_upwards [hy_top.eventually_ge_atTop 2, hL.eventually_ge_atTop 2] with x hy2 hL2
        have hfl1 : (1 : ℝ) ≤ (⌊y x⌋₊ : ℝ) := by
          exact_mod_cast (Nat.le_floor (by norm_num; linarith : ((1 : ℕ) : ℝ) ≤ y x))
        have hden : 0 < (L x) ^ 20 - 1 := by
          have : (2 : ℝ) ^ 20 ≤ (L x) ^ 20 := pow_le_pow_left₀ (by norm_num) hL2 20
          norm_num at this; linarith
        exact div_nonneg (div_nonneg (Real.log_nonneg hfl1) (Real.log_pos (by norm_num)).le) hden.le
      · filter_upwards [hy_top.eventually_ge_atTop 2, hL.eventually_ge_atTop 2,
          hlogy_div_L.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))] with x hy2 hL2 hly2
        have hfl_pos : 0 < (⌊y x⌋₊ : ℝ) := by
          exact_mod_cast (Nat.le_floor (by norm_num; linarith : ((1 : ℕ) : ℝ) ≤ y x))
        have hlogfl_le : Real.log (⌊y x⌋₊ : ℝ) ≤ 2 * L x := by
          have h1 : Real.log (⌊y x⌋₊ : ℝ) ≤ Real.log (y x) :=
            Real.log_le_log hfl_pos (Nat.floor_le (by linarith))
          have h2 : Real.log (y x) ≤ 2 * L x := (div_le_iff₀ (by linarith : 0 < L x)).mp hly2.le
          linarith
        have hden_ge : (L x) ^ 2 ≤ (L x) ^ 20 - 1 := by
          have hpow : (L x) ^ 2 * 4 ≤ (L x) ^ 20 := by
            have h18 : (4 : ℝ) ≤ (L x) ^ 18 := by
              have : (2 : ℝ) ^ 18 ≤ (L x) ^ 18 := pow_le_pow_left₀ (by norm_num) hL2 18
              norm_num at this; linarith
            calc (L x) ^ 2 * 4 ≤ (L x) ^ 2 * (L x) ^ 18 :=
                  mul_le_mul_of_nonneg_left h18 (sq_nonneg _)
              _ = (L x) ^ 20 := by ring
          nlinarith
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        calc (Real.log (⌊y x⌋₊ : ℝ) / Real.log 2) / ((L x) ^ 20 - 1)
            ≤ (2 * L x / Real.log 2) / ((L x) ^ 2) := by
              apply div_le_div₀ (by positivity)
                (div_le_div_of_nonneg_right hlogfl_le hlog2.le) (by positivity) hden_ge
          _ = (2 / Real.log 2) / L x := by field_simp [(by linarith : L x ≠ 0), hlog2.ne']
    have hcomp := (Real.continuous_exp.tendsto 0).comp harg
    rw [Real.exp_zero] at hcomp
    exact hcomp
  filter_upwards [hy_top.eventually_ge_atTop 2, hL.eventually_ge_atTop 2,
    hU.eventually_gt_atTop 0, hlogU.eventually_gt_atTop 0, hX.eventually_gt_atTop 0,
    hS_eq, hV_bounds,
    hprod_lim.eventually (Ioo_mem_nhds (by norm_num : (95 / 100 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 105 / 100)),
    hexp_lim.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 1 + 1 / 128)),
    (hXU_div_L.const_mul_atTop (show 0 < 60 * c by positivity)).eventually_ge_atTop 128]
    with x hy2 hL2 hUp hlogUp hXp hSeq ⟨hV_lo, hV_hi⟩ ⟨hpr_lo, hpr_hi⟩ hexp hbig
  dsimp only
  have hy_pos_floor : 0 < ⌊y x⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hL20_gt : 1 < (L x) ^ 20 := by
    have : (2 : ℝ) ^ 20 ≤ (L x) ^ 20 := pow_le_pow_left₀ (by norm_num) hL2 20
    norm_num at this; linarith
  have hprod_lo : (95 / 100 : ℝ) * (80 * (U x) ^ 2 / (L x * Real.log (U x))) ≤
      ∏ p ∈ (v x).primesLE \ (u x).primesLE, (1 - 1 / (p : ℝ)) := by
    have h2 : (95 / 100 : ℝ) ≤
        (∏ p ∈ (v x).primesLE \ (u x).primesLE, (1 - 1 / (p : ℝ))) *
          (L x * Real.log (U x) / (80 * (U x) ^ 2)) := hpr_lo.le
    have hmul := mul_le_mul_of_nonneg_right h2
      (show 0 ≤ 80 * (U x) ^ 2 / (L x * Real.log (U x)) by positivity)
    have ec : (L x * Real.log (U x) / (80 * (U x) ^ 2)) *
        (80 * (U x) ^ 2 / (L x * Real.log (U x))) = 1 := by
      field_simp [(by linarith : L x ≠ 0), hUp.ne', hlogUp.ne']
    rw [mul_assoc, ec, mul_one] at hmul
    exact hmul
  have hprod_hi : ∏ p ∈ (v x).primesLE \ (u x).primesLE, (1 - 1 / (p : ℝ)) ≤
      (105 / 100 : ℝ) * (80 * (U x) ^ 2 / (L x * Real.log (U x))) := by
    have h2 : (∏ p ∈ (v x).primesLE \ (u x).primesLE, (1 - 1 / (p : ℝ))) *
        (L x * Real.log (U x) / (80 * (U x) ^ 2)) ≤ 105 / 100 := hpr_hi.le
    have hmul := mul_le_mul_of_nonneg_right h2
      (show 0 ≤ 80 * (U x) ^ 2 / (L x * Real.log (U x)) by positivity)
    have ec : (L x * Real.log (U x) / (80 * (U x) ^ 2)) *
        (80 * (U x) ^ 2 / (L x * Real.log (U x))) = 1 := by
      field_simp [(by linarith : L x ≠ 0), hUp.ne', hlogUp.ne']
    rw [mul_assoc, ec, mul_one] at hmul
    exact hmul
  have hscale_eq :
      (c * X x * Real.log (U x) / U x) * (80 * (U x) ^ 2 / (L x * Real.log (U x))) =
        80 * c * (X x * U x / L x) := by
    field_simp [(by linarith : L x ≠ 0), hUp.ne', hlogUp.ne']
  have hscale_nn : 0 ≤ c * (X x * U x / L x) := by positivity
  have hM_lo : 60 * c * (X x * U x / L x) ≤
      (((Finset.Ioc x ⌊y x⌋₊).filter Nat.Prime).card : ℝ) *
        ∏ p ∈ (v x).primesLE \ (u x).primesLE, (1 - 1 / (p : ℝ)) := by
    have hmul := mul_le_mul hV_lo hprod_lo (by positivity) (by positivity)
    calc 60 * c * (X x * U x / L x)
        ≤ (85 / 100 : ℝ) * (95 / 100 : ℝ) * (80 * c * (X x * U x / L x)) := by nlinarith
      _ = ((85 / 100 : ℝ) * (c * X x * Real.log (U x) / U x)) *
            ((95 / 100 : ℝ) * (80 * (U x) ^ 2 / (L x * Real.log (U x)))) := by
          rw [← hscale_eq]; ring
      _ ≤ _ := hmul
  have hM_hi :
      (((Finset.Ioc x ⌊y x⌋₊).filter Nat.Prime).card : ℝ) *
        ∏ p ∈ (v x).primesLE \ (u x).primesLE, (1 - 1 / (p : ℝ)) ≤
      100 * c * (X x * U x / L x) := by
    have hV_nn : 0 ≤ (((Finset.Ioc x ⌊y x⌋₊).filter Nat.Prime).card : ℝ) := Nat.cast_nonneg _
    have hpr_nn : 0 ≤ ∏ p ∈ (v x).primesLE \ (u x).primesLE, (1 - 1 / (p : ℝ)) := by
      apply Finset.prod_nonneg
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1).two_le
      have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      linarith
    have hmul := mul_le_mul hV_hi hprod_hi hpr_nn (by positivity)
    calc _ ≤ ((115 / 100 : ℝ) * (c * X x * Real.log (U x) / U x)) *
            ((105 / 100 : ℝ) * (80 * (U x) ^ 2 / (L x * Real.log (U x)))) := hmul
      _ = (115 / 100 : ℝ) * (105 / 100 : ℝ) * (80 * c * (X x * U x / L x)) := by
          rw [← hscale_eq]; ring
      _ ≤ 100 * c * (X x * U x / L x) := by nlinarith
  have hM_128 : 128 ≤
      (((Finset.Ioc x ⌊y x⌋₊).filter Nat.Prime).card : ℝ) *
        ∏ p ∈ (v x).primesLE \ (u x).primesLE, (1 - 1 / (p : ℝ)) := by
    have hbig' : 128 ≤ 60 * c * (X x * U x / L x) := hbig
    linarith
  change 0 < ⌊y x⌋₊ ∧ 1 < (L x) ^ 20 ∧
    Real.exp ((Real.log (⌊y x⌋₊ : ℝ) / Real.log 2) / ((L x) ^ 20 - 1)) ≤ 1 + 1 / 128 ∧
    128 ≤ (((Finset.Ioc x ⌊y x⌋₊).filter Nat.Prime).card : ℝ) *
      ∏ p ∈ (Finset.range (⌊z x⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ p ∉ (Finset.Ioc (x / 2) x).filter Nat.Prime ∧ (L x) ^ 20 < p),
        (1 - 1 / (p : ℝ)) ∧
    60 * c * (X x * U x / L x) ≤
      (((Finset.Ioc x ⌊y x⌋₊).filter Nat.Prime).card : ℝ) *
        ∏ p ∈ (Finset.range (⌊z x⌋₊ + 1)).filter
          (fun p : ℕ => p.Prime ∧ p ∉ (Finset.Ioc (x / 2) x).filter Nat.Prime ∧ (L x) ^ 20 < p),
          (1 - 1 / (p : ℝ)) ∧
    (((Finset.Ioc x ⌊y x⌋₊).filter Nat.Prime).card : ℝ) *
      ∏ p ∈ (Finset.range (⌊z x⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ p ∉ (Finset.Ioc (x / 2) x).filter Nat.Prime ∧ (L x) ^ 20 < p),
        (1 - 1 / (p : ℝ)) ≤
    100 * c * (X x * U x / L x)
  rw [hSeq]
  exact ⟨hy_pos_floor, hL20_gt, hexp.le, hM_128, hM_lo, hM_hi⟩

end PreliminarySieveMoment

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1.H1 :=
  PreliminarySieveMoment.main_sieve_bound
