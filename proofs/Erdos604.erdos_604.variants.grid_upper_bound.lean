import FormalConjectures.ErdosProblems.«604»
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Upper bound for Erdős Problem 604 (Pinned Distinct Distances on the Grid)

We prove `Erdos604.erdos_604.variants.grid_upper_bound` completely elementarily via:
1. Chebyshev/Mertens upper bound for primes congruent to `1 mod 4`,
2. Lower bound for Selberg's sieve denominator `S(z) ≫ √(log z)`,
3. Selberg's `Λ²` sieve upper bound for integers with no prime factor `≡ 3 mod 4`,
4. Landau-type upper bound `O(X / √(log X))` on sums of two squares up to `X`,
5. The `⌈√n⌉ × ⌈√n⌉` integer grid construction in `ℝ²`.
-/

open Filter Finset
open scoped EuclideanGeometry ArithmeticFunction ArithmeticFunction.Moebius

namespace Erdos604GridUpperBound

/- ### Section 1: Elementary Chebyshev/Mertens upper bound for primes ≡ 1 (mod 4) -/

/-- The non-principal Dirichlet character modulo 4. -/
private def chi4 (n : ℕ) : ℝ :=
  if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

private lemma chi4_zero : chi4 0 = 0 := by simp [chi4]
private lemma chi4_one : chi4 1 = 1 := by simp [chi4]
private lemma chi4_two : chi4 2 = 0 := by simp [chi4]

private lemma chi4_mul (a b : ℕ) : chi4 (a * b) = chi4 a * chi4 b := by
  unfold chi4
  have h : (a * b) % 4 = ((a % 4) * (b % 4)) % 4 := Nat.mul_mod a b 4
  rw [h]
  have ha : a % 4 < 4 := Nat.mod_lt a (by decide)
  have hb : b % 4 < 4 := Nat.mod_lt b (by decide)
  interval_cases (a % 4) <;> interval_cases (b % 4) <;> norm_num

private lemma chi4_even (k : ℕ) : chi4 (2 * k) = 0 := by
  unfold chi4
  have : (2 * k) % 4 = 0 ∨ (2 * k) % 4 = 2 := by omega
  rcases this with h | h <;> simp [h]

private lemma chi4_odd (k : ℕ) : chi4 (2 * k + 1) = (-1 : ℝ) ^ k := by
  unfold chi4
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have h1 : (2 * (m + m) + 1) % 4 = 1 := by omega
    rw [if_pos h1, show m + m = 2 * m by omega, pow_mul]
    norm_num
  · have h3 : (2 * (2 * m + 1) + 1) % 4 = 3 := by omega
    have h1 : (2 * (2 * m + 1) + 1) % 4 ≠ 1 := by omega
    rw [if_neg h1, if_pos h3, pow_succ, pow_mul]
    norm_num

private lemma abs_chi4_le_one (n : ℕ) : |chi4 n| ≤ 1 := by
  unfold chi4
  split_ifs <;> norm_num

/-- Alternating sum of a nonneg antitone sequence on `Ico a b` lies in `[0, f a]`. -/
private lemma alternating_sum_bounds (f : ℕ → ℝ) :
    ∀ n a b : ℕ, b - a = n →
      (∀ k, a ≤ k → k < b → 0 ≤ f k) →
      (∀ k, a ≤ k → k + 1 < b → f (k + 1) ≤ f k) →
      0 ≤ ∑ k ∈ Finset.Ico a b, (-1 : ℝ) ^ (k - a) * f k ∧
        ∑ k ∈ Finset.Ico a b, (-1 : ℝ) ^ (k - a) * f k ≤ if a < b then f a else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b hba hnn hanti
    rcases n with _ | _ | m
    · have hab : b ≤ a := by omega
      rw [Finset.Ico_eq_empty (not_lt.mpr hab), Finset.sum_empty, if_neg (not_lt.mpr hab)]
      exact ⟨le_rfl, le_rfl⟩
    · have hb : b = a + 1 := by omega
      subst hb
      rw [Nat.Ico_succ_singleton, Finset.sum_singleton, Nat.sub_self, pow_zero, one_mul,
        if_pos (Nat.lt_succ_self a)]
      exact ⟨hnn a le_rfl (Nat.lt_succ_self a), le_rfl⟩
    · have hab2 : a + 2 ≤ b := by omega
      have h1 : Finset.Ico a b = insert a (insert (a + 1) (Finset.Ico (a + 2) b)) := by
        ext k
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      have ha_not : a ∉ insert (a + 1) (Finset.Ico (a + 2) b) := by
        simp only [Finset.mem_insert, Finset.mem_Ico]
        omega
      have ha1_not : a + 1 ∉ Finset.Ico (a + 2) b := by
        simp only [Finset.mem_Ico]
        omega
      rw [h1, Finset.sum_insert ha_not, Finset.sum_insert ha1_not]
      have htail_eq :
          ∑ k ∈ Finset.Ico (a + 2) b, (-1 : ℝ) ^ (k - a) * f k =
            ∑ k ∈ Finset.Ico (a + 2) b, (-1 : ℝ) ^ (k - (a + 2)) * f k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk2 : a + 2 ≤ k := (Finset.mem_Ico.mp hk).1
        rw [show k - a = (k - (a + 2)) + 2 by omega, pow_add]
        norm_num
      rw [htail_eq]
      have hsub : b - (a + 2) = m := by omega
      obtain ⟨ht0, ht1⟩ := ih m (by omega) (a + 2) b hsub
        (fun k hk1 hk2 => hnn k (by omega) hk2)
        (fun k hk1 hk2 => hanti k (by omega) hk2)
      have ha_sub : a - a = 0 := Nat.sub_self a
      have ha1_sub : a + 1 - a = 1 := by omega
      rw [ha_sub, ha1_sub, pow_zero, one_mul, pow_one, neg_one_mul]
      have hfa1 : f (a + 1) ≤ f a := hanti a le_rfl (by omega)
      have hfa1_nn : 0 ≤ f (a + 1) := hnn (a + 1) (by omega) (by omega)
      rw [if_pos (by omega : a < b)]
      refine ⟨by linarith, ?_⟩
      by_cases hlt : a + 2 < b
      · rw [if_pos hlt] at ht1
        have hfa2 : f (a + 2) ≤ f (a + 1) := hanti (a + 1) (by omega) hlt
        linarith
      · rw [if_neg hlt] at ht1
        linarith

private lemma sum_Ico_sub_succ (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (f k - f (k + 1)) = f a - f b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha; simp
  | succ n ih =>
    by_cases h : a = n + 1
    · subst h; simp
    · rw [Finset.sum_Ico_succ_top (by omega : a ≤ n), ih (by omega)]
      ring

private lemma sum_Ico_succ_sub (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (f (k + 1) - f k) = f b - f a := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha; simp
  | succ n ih =>
    by_cases h : a = n + 1
    · subst h; simp
    · rw [Finset.sum_Ico_succ_top (by omega : a ≤ n), ih (by omega)]
      ring

private lemma sum_chi4_eq_sum_odd (g : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, chi4 n * g n =
      ∑ k ∈ Finset.Ico 0 ((N + 1) / 2), (-1 : ℝ) ^ k * g (2 * k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
    rw [hIcc, Finset.sum_insert hnot, ih]
    rcases Nat.even_or_odd (N + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hdiv : (N + 1 + 1) / 2 = (N + 1) / 2 := by omega
      rw [hdiv, show N + 1 = 2 * m by omega, chi4_even, zero_mul, zero_add]
    · have hdiv1 : (N + 1) / 2 = m := by omega
      have hdiv2 : (N + 1 + 1) / 2 = m + 1 := by omega
      rw [hdiv1, hdiv2, show N + 1 = 2 * m + 1 by omega, chi4_odd,
        Finset.sum_Ico_succ_top (Nat.zero_le m), add_comm]

private noncomputable def L4 (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, chi4 n * (1 / (n : ℝ))

private lemma L4_diff_abs_le {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    |L4 M - L4 N| ≤ 1 / (N : ℝ) := by
  unfold L4
  rw [sum_chi4_eq_sum_odd, sum_chi4_eq_sum_odd]
  have hle : (N + 1) / 2 ≤ (M + 1) / 2 := Nat.div_le_div_right (Nat.add_le_add_right hNM 1)
  have hsplit := Finset.sum_Ico_consecutive (f := fun k => (-1 : ℝ) ^ k * (1 / ((2 * k + 1 : ℕ) : ℝ)))
    (Nat.zero_le ((N + 1) / 2)) hle
  have hdiff :
      ∑ k ∈ Finset.Ico 0 ((M + 1) / 2), (-1 : ℝ) ^ k * (1 / ((2 * k + 1 : ℕ) : ℝ)) -
        ∑ k ∈ Finset.Ico 0 ((N + 1) / 2), (-1 : ℝ) ^ k * (1 / ((2 * k + 1 : ℕ) : ℝ)) =
      ∑ k ∈ Finset.Ico ((N + 1) / 2) ((M + 1) / 2),
        (-1 : ℝ) ^ k * (1 / ((2 * k + 1 : ℕ) : ℝ)) := by linarith
  rw [hdiff]
  set a := (N + 1) / 2
  set b := (M + 1) / 2
  have hfac :
      ∑ k ∈ Finset.Ico a b, (-1 : ℝ) ^ k * (1 / ((2 * k + 1 : ℕ) : ℝ)) =
        (-1 : ℝ) ^ a * ∑ k ∈ Finset.Ico a b, (-1 : ℝ) ^ (k - a) * (1 / ((2 * k + 1 : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hka : a ≤ k := (Finset.mem_Ico.mp hk).1
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hka]
  rw [hfac, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  obtain ⟨h0, h1⟩ := alternating_sum_bounds (fun k => 1 / ((2 * k + 1 : ℕ) : ℝ)) (b - a) a b rfl
    (fun k _ _ => by positivity)
    (fun k _ _ => by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * (k + 1) + 1))
  rw [abs_of_nonneg h0]
  refine h1.trans ?_
  split_ifs
  · apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (by omega : N ≤ 2 * a + 1)
  · positivity

private lemma L4_bounds {N : ℕ} (hN : 1 ≤ N) : (2 : ℝ) / 3 ≤ L4 N ∧ L4 N ≤ 1 := by
  unfold L4
  rw [sum_chi4_eq_sum_odd]
  set b := (N + 1) / 2
  have hb : 1 ≤ b := by omega
  obtain ⟨_, hup⟩ := alternating_sum_bounds (fun k => 1 / ((2 * k + 1 : ℕ) : ℝ)) b 0 b (by omega)
    (fun k _ _ => by positivity)
    (fun k _ _ => by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * (k + 1) + 1))
  have hup' : ∑ k ∈ Finset.Ico 0 b, (-1 : ℝ) ^ k * (1 / ((2 * k + 1 : ℕ) : ℝ)) ≤ 1 := by
    simp only [Nat.sub_zero, if_pos (by omega : 0 < b)] at hup
    exact hup.trans (by norm_num)
  refine ⟨?_, hup'⟩
  by_cases hb1 : b = 1
  · rw [hb1, Nat.Ico_succ_singleton, Finset.sum_singleton]
    norm_num
  · have hb2 : 2 ≤ b := by omega
    have hsplit : Finset.Ico 0 b = insert 0 (insert 1 (Finset.Ico 2 b)) := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    have htail_eq :
        ∑ k ∈ Finset.Ico 2 b, (-1 : ℝ) ^ k * (1 / ((2 * k + 1 : ℕ) : ℝ)) =
          ∑ k ∈ Finset.Ico 2 b, (-1 : ℝ) ^ (k - 2) * (1 / ((2 * k + 1 : ℕ) : ℝ)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
      rw [show k = (k - 2) + 2 by omega, pow_add]
      norm_num
    rw [htail_eq]
    obtain ⟨h0, _⟩ := alternating_sum_bounds (fun k => 1 / ((2 * k + 1 : ℕ) : ℝ)) (b - 2) 2 b rfl
      (fun k _ _ => by positivity)
      (fun k _ _ => by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * (k + 1) + 1))
    have h01 :
        (-1 : ℝ) ^ 0 * (1 / ((2 * 0 + 1 : ℕ) : ℝ)) +
          (-1 : ℝ) ^ 1 * (1 / ((2 * 1 + 1 : ℕ) : ℝ)) = 2 / 3 := by norm_num
    linarith

private lemma one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  have hexp : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) hexp

private lemma log_div_self_anti {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    Real.log y / y ≤ Real.log x / x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hlogx : 1 ≤ Real.log x :=
    le_trans one_lt_log_three.le (Real.log_le_log (by norm_num) hx)
  have hsub : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  rw [Real.log_div hy0.ne' hx0.ne'] at hsub
  have h1 : x * (Real.log y - Real.log x) ≤ x * (y / x - 1) :=
    mul_le_mul_of_nonneg_left hsub hx0.le
  have h2 : x * (y / x - 1) = y - x := by field_simp
  rw [h2] at h1
  have h3 : (y - x) * 1 ≤ (y - x) * Real.log x :=
    mul_le_mul_of_nonneg_left hlogx (by linarith)
  rw [div_le_div_iff₀ hy0 hx0]
  nlinarith

private noncomputable def M4 (z : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 z, chi4 n * (Real.log (n : ℝ) / (n : ℝ))

private lemma abs_M4_le_one (z : ℕ) : |M4 z| ≤ 1 := by
  unfold M4
  rw [sum_chi4_eq_sum_odd]
  set b := (z + 1) / 2
  by_cases hb : b = 0
  · rw [hb]; simp
  · have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb
    have hsplit : Finset.Ico 0 b = insert 0 (Finset.Ico 1 b) := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    simp only [Nat.cast_one, Real.log_one, zero_div, mul_zero, zero_add]
    have hfac :
        ∑ k ∈ Finset.Ico 1 b, (-1 : ℝ) ^ k * (Real.log ((2 * k + 1 : ℕ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) =
          (-1 : ℝ) * ∑ k ∈ Finset.Ico 1 b,
            (-1 : ℝ) ^ (k - 1) * (Real.log ((2 * k + 1 : ℕ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
      rw [← mul_assoc, show (-1 : ℝ) * (-1 : ℝ) ^ (k - 1) = (-1 : ℝ) ^ (1 + (k - 1)) by
        rw [pow_add, pow_one], Nat.add_sub_cancel' hk1]
    rw [hfac, abs_mul, abs_neg, abs_one, one_mul]
    obtain ⟨h0, h1⟩ := alternating_sum_bounds
      (fun k => Real.log ((2 * k + 1 : ℕ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) (b - 1) 1 b rfl
      (fun k hk _ => div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * k + 1))) (by positivity))
      (fun k hk _ => log_div_self_anti (by exact_mod_cast (by omega : 3 ≤ 2 * k + 1))
        (by exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * (k + 1) + 1)))
    rw [abs_of_nonneg h0]
    refine h1.trans ?_
    split_ifs
    · have hlog3 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
        linarith
      norm_num
      linarith
    · norm_num

private lemma M4_eq_sum_vonMangoldt (z : ℕ) :
    M4 z = ∑ d ∈ Finset.Icc 1 z, (chi4 d * Λ d / (d : ℝ)) * L4 (z / d) := by
  unfold M4 L4
  have hstep1 :
      ∑ n ∈ Finset.Icc 1 z, chi4 n * (Real.log (n : ℝ) / (n : ℝ)) =
        ∑ n ∈ Finset.Icc 1 z, ∑ d ∈ n.divisors, chi4 n * Λ d / (n : ℝ) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← ArithmeticFunction.vonMangoldt_sum, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [hstep1]
  have hstep2 :
      ∑ d ∈ Finset.Icc 1 z, (chi4 d * Λ d / (d : ℝ)) *
          ∑ m ∈ Finset.Icc 1 (z / d), chi4 m * (1 / (m : ℝ)) =
        ∑ d ∈ Finset.Icc 1 z, ∑ m ∈ Finset.Icc 1 (z / d),
          chi4 (d * m) * Λ d / ((d * m : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [chi4_mul, Nat.cast_mul]
    ring
  rw [hstep2, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ => ⟨p.2, p.1 / p.2⟩) ?_ ?_ ?_ ?_
  · intro ⟨n, d⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨hn1, hnz⟩, ⟨hdn, hn0⟩⟩ := hp
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdn (by omega)
    have hdz : d ≤ z := le_trans (Nat.le_of_dvd (by omega) hdn) hnz
    have hdiv1 : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdn) (by omega)
    have hdivz : n / d ≤ z / d := Nat.div_le_div_right hnz
    exact ⟨⟨hd1, hdz⟩, ⟨hdiv1, hdivz⟩⟩
  · intro ⟨n₁, d₁⟩ hp₁ ⟨n₂, d₂⟩ hp₂ heq
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
    obtain ⟨rfl, hdiv⟩ := heq
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp₁ hp₂
    have hn₁ : d₁ * (n₁ / d₁) = n₁ := Nat.mul_div_cancel' hp₁.2.1
    have hn₂ : d₁ * (n₂ / d₁) = n₂ := Nat.mul_div_cancel' hp₂.2.1
    have : n₁ = n₂ := by rw [← hn₁, ← hn₂, hdiv]
    subst this; rfl
  · intro ⟨d, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
    obtain ⟨⟨hd1, hdz⟩, ⟨hm1, hmz⟩⟩ := hp
    have hdm_le : d * m ≤ z := le_trans (Nat.mul_le_mul_left d hmz) (Nat.mul_div_le z d)
    have hdm_pos : 1 ≤ d * m := Nat.mul_pos hd1 hm1
    refine ⟨⟨d * m, d⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
      exact ⟨⟨hdm_pos, hdm_le⟩, ⟨dvd_mul_right d m, by omega⟩⟩
    · simp [Nat.mul_div_cancel_left m (by omega : 0 < d)]
  · intro ⟨n, d⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    simp only [Nat.mul_div_cancel' hp.2.1]

private lemma sum_log_primes_le (z : ℕ) :
    ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Real.log (p : ℝ) ≤ 2 * (z : ℝ) := by
  have hprod_eq :
      ∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (p : ℝ) = (primorial z : ℝ) := by
    rw [primorial, Nat.cast_prod]
    refine Finset.prod_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hpz⟩, hp⟩; exact ⟨by omega, hp⟩
    · rintro ⟨hpz, hp⟩; exact ⟨⟨hp.one_lt.le, by omega⟩, hp⟩
  have hsum_eq :
      ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Real.log (p : ℝ) = Real.log (primorial z : ℝ) := by
    rw [← hprod_eq, Real.log_prod]
    intro p hp
    exact Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.ne_zero
  rw [hsum_eq]
  have hprim : (primorial z : ℝ) ≤ (4 : ℝ) ^ z := by
    exact_mod_cast primorial_le_four_pow z
  have hlog : Real.log (primorial z : ℝ) ≤ (z : ℝ) * Real.log 4 := by
    calc Real.log (primorial z : ℝ) ≤ Real.log ((4 : ℝ) ^ z) :=
          Real.log_le_log (by exact_mod_cast primorial_pos z) hprim
      _ = (z : ℝ) * Real.log 4 := Real.log_pow 4 z
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have h2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have : Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
    rw [this, Real.log_pow]
    push_cast
    linarith
  nlinarith

private lemma sum_vonMangoldt_le (z : ℕ) :
    ∑ d ∈ Finset.Icc 1 z, Λ d ≤ 4 * (z : ℝ) := by
  by_cases hz : z = 0
  · simp [hz]
  have hz1 : 1 ≤ z := Nat.pos_of_ne_zero hz
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 z) Nat.Prime]
  have h1 : ∑ d ∈ (Finset.Icc 1 z).filter Nat.Prime, Λ d ≤ 2 * (z : ℝ) := by
    calc ∑ d ∈ (Finset.Icc 1 z).filter Nat.Prime, Λ d
        = ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Real.log (p : ℝ) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2
      _ ≤ 2 * (z : ℝ) := sum_log_primes_le z
  have h2 : ∑ d ∈ (Finset.Icc 1 z).filter (fun d => ¬ d.Prime), Λ d ≤ 2 * (z : ℝ) := by
    set S := (Finset.Icc 1 z).filter (fun d => ¬ d.Prime ∧ IsPrimePow d)
    have hS : ∑ d ∈ (Finset.Icc 1 z).filter (fun d => ¬ d.Prime), Λ d = ∑ d ∈ S, Λ d := by
      symm
      refine Finset.sum_subset (fun d hd => by
        simp only [S, Finset.mem_filter] at hd ⊢; exact ⟨hd.1, hd.2.1⟩) ?_
      intro d hd hnot
      simp only [S, Finset.mem_filter] at hd hnot
      have hnp : ¬ IsPrimePow d := fun h => hnot ⟨hd.1, hd.2, h⟩
      exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp
    rw [hS]
    have hmaps : ∀ d ∈ S, d.minFac ∈ (Finset.Icc 1 (Nat.sqrt z)).filter Nat.Prime := by
      intro d hd
      simp only [S, Finset.mem_filter, Finset.mem_Icc] at hd ⊢
      obtain ⟨⟨hd1, hdz⟩, hnp, hpp⟩ := hd
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff d).mp hpp
      have hk2 : 2 ≤ k := by
        by_contra hlt
        have hk1 : k = 1 := by omega
        subst hk1
        exact hnp (by simpa using hp)
      have hmin : (p ^ k).minFac = p := by
        rw [Nat.pow_minFac (by omega), hp.minFac_eq]
      rw [hmin]
      have hp2 : p * p ≤ z := by
        calc p * p = p ^ 2 := (sq p).symm
          _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
          _ ≤ z := hdz
      exact ⟨⟨hp.one_lt.le, Nat.le_sqrt.mpr hp2⟩, hp⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hfiber : ∀ p ∈ (Finset.Icc 1 (Nat.sqrt z)).filter Nat.Prime,
        ∑ d ∈ S.filter (fun d => d.minFac = p), Λ d ≤ Real.log (z : ℝ) := by
      intro p hp
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      have hsub : S.filter (fun d => d.minFac = p) ⊆
          (Finset.Icc 1 (Nat.log p z)).image (fun k => p ^ k) := by
        intro d hd
        simp only [S, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image] at hd ⊢
        obtain ⟨⟨⟨_, hdz⟩, _, hpp⟩, hmin⟩ := hd
        obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff d).mp hpp
        have hqp : q = p := by
          rw [Nat.pow_minFac hk.ne', hq.minFac_eq] at hmin
          exact hmin
        subst hqp
        exact ⟨k, ⟨hk, Nat.le_log_of_pow_le hpPrime.one_lt hdz⟩, rfl⟩
      have hcard : #(S.filter (fun d => d.minFac = p)) ≤ Nat.log p z := by
        calc #(S.filter (fun d => d.minFac = p))
            ≤ #((Finset.Icc 1 (Nat.log p z)).image (fun k => p ^ k)) := Finset.card_le_card hsub
          _ ≤ #(Finset.Icc 1 (Nat.log p z)) := Finset.card_image_le
          _ = Nat.log p z := by simp
      calc ∑ d ∈ S.filter (fun d => d.minFac = p), Λ d
          = ∑ d ∈ S.filter (fun d => d.minFac = p), Real.log (p : ℝ) := by
            refine Finset.sum_congr rfl fun d hd => ?_
            simp only [S, Finset.mem_filter] at hd
            rw [ArithmeticFunction.vonMangoldt_apply, if_pos hd.1.2.2, hd.2]
        _ = (#(S.filter (fun d => d.minFac = p)) : ℝ) * Real.log (p : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Nat.log p z : ℝ) * Real.log (p : ℝ) := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
              (Real.log_nonneg (by exact_mod_cast hpPrime.one_lt.le))
        _ = Real.log (((p ^ Nat.log p z : ℕ) : ℝ)) := by
            rw [Nat.cast_pow, Real.log_pow]
        _ ≤ Real.log (z : ℝ) := by
            apply Real.log_le_log
            · exact_mod_cast pow_pos hpPrime.pos _
            · exact_mod_cast Nat.pow_log_le_self p hz
    calc ∑ p ∈ (Finset.Icc 1 (Nat.sqrt z)).filter Nat.Prime,
            ∑ d ∈ S.filter (fun d => d.minFac = p), Λ d
        ≤ ∑ _p ∈ (Finset.Icc 1 (Nat.sqrt z)).filter Nat.Prime, Real.log (z : ℝ) :=
          Finset.sum_le_sum hfiber
      _ = (#((Finset.Icc 1 (Nat.sqrt z)).filter Nat.Prime) : ℝ) * Real.log (z : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Nat.sqrt z : ℝ) * Real.log (z : ℝ) := by
          have hc : #((Finset.Icc 1 (Nat.sqrt z)).filter Nat.Prime) ≤ Nat.sqrt z := by
            calc #((Finset.Icc 1 (Nat.sqrt z)).filter Nat.Prime)
                ≤ #(Finset.Icc 1 (Nat.sqrt z)) := Finset.card_filter_le _ _
              _ = Nat.sqrt z := by simp
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
            (Real.log_nonneg (by exact_mod_cast hz1))
      _ ≤ Real.sqrt (z : ℝ) * (2 * Real.sqrt (z : ℝ)) := by
          have hsq : (Nat.sqrt z : ℝ) ≤ Real.sqrt (z : ℝ) := by
            rw [Real.le_sqrt (by positivity) (by positivity), sq]
            exact_mod_cast Nat.sqrt_le z
          have hlog : Real.log (z : ℝ) ≤ 2 * Real.sqrt (z : ℝ) := by
            have hsqpos : 0 < Real.sqrt (z : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hz1)
            have hle := Real.log_le_sub_one_of_pos hsqpos
            have hlog_eq : Real.log (z : ℝ) = 2 * Real.log (Real.sqrt (z : ℝ)) := by
              calc Real.log (z : ℝ) = Real.log ((Real.sqrt (z : ℝ)) ^ 2) := by
                    rw [Real.sq_sqrt (by positivity)]
                _ = 2 * Real.log (Real.sqrt (z : ℝ)) := by rw [Real.log_pow]; push_cast; ring
            linarith
          exact mul_le_mul hsq hlog (Real.log_nonneg (by exact_mod_cast hz1)) (Real.sqrt_nonneg _)
      _ = 2 * (z : ℝ) := by
          have : Real.sqrt (z : ℝ) * Real.sqrt (z : ℝ) = (z : ℝ) :=
            Real.mul_self_sqrt (by positivity)
          linarith
  linarith

private lemma abs_sum_chi4_vonMangoldt_div_le (z : ℕ) :
    |∑ d ∈ Finset.Icc 1 z, chi4 d * Λ d / (d : ℝ)| ≤ 14 := by
  by_cases hz : z = 0
  · simp [hz]
  have hz1 : 1 ≤ z := Nat.pos_of_ne_zero hz
  have hdiff :
      |M4 z - L4 z * ∑ d ∈ Finset.Icc 1 z, chi4 d * Λ d / (d : ℝ)| ≤ 8 := by
    rw [M4_eq_sum_vonMangoldt, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc |∑ d ∈ Finset.Icc 1 z, ((chi4 d * Λ d / (d : ℝ)) * L4 (z / d) -
              L4 z * (chi4 d * Λ d / (d : ℝ)))|
        ≤ ∑ d ∈ Finset.Icc 1 z, |(chi4 d * Λ d / (d : ℝ)) * (L4 (z / d) - L4 z)| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
          refine Finset.sum_congr rfl fun d _ => by ring_nf
      _ ≤ ∑ d ∈ Finset.Icc 1 z, (2 / (z : ℝ)) * Λ d := by
          refine Finset.sum_le_sum fun d hd => ?_
          simp only [Finset.mem_Icc] at hd
          obtain ⟨hd1, hdz⟩ := hd
          have hzd1 : 1 ≤ z / d := Nat.div_pos hdz (by omega)
          have hzd_le : z / d ≤ z := Nat.div_le_self z d
          have hL : |L4 (z / d) - L4 z| ≤ 1 / ((z / d : ℕ) : ℝ) := by
            rw [abs_sub_comm]
            exact L4_diff_abs_le hzd1 hzd_le
          have h2d : (z : ℝ) ≤ 2 * (d : ℝ) * ((z / d : ℕ) : ℝ) := by
            have hnat : z < d * (z / d + 1) := by
              have := Nat.div_add_mod z d
              have := Nat.mod_lt z (by omega : 0 < d)
              nlinarith
            have hnat2 : z ≤ 2 * d * (z / d) := by nlinarith
            exact_mod_cast hnat2
          have hinv : 1 / ((z / d : ℕ) : ℝ) ≤ 2 * (d : ℝ) / (z : ℝ) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            linarith
          have habs : |chi4 d * Λ d / (d : ℝ)| ≤ Λ d / (d : ℝ) := by
            rw [abs_div, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
              abs_of_pos (by positivity : (0 : ℝ) < d)]
            have := abs_chi4_le_one d
            have hnn : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
            have hdpos : (0 : ℝ) < d := by positivity
            rw [div_le_div_iff_of_pos_right hdpos]
            nlinarith
          rw [abs_mul]
          calc |chi4 d * Λ d / (d : ℝ)| * |L4 (z / d) - L4 z|
              ≤ (Λ d / (d : ℝ)) * (2 * (d : ℝ) / (z : ℝ)) := by
                exact mul_le_mul habs (hL.trans hinv) (abs_nonneg _) (by positivity)
            _ = (2 / (z : ℝ)) * Λ d := by
                have hd0 : (d : ℝ) ≠ 0 := by positivity
                field_simp
      _ = (2 / (z : ℝ)) * ∑ d ∈ Finset.Icc 1 z, Λ d := (Finset.mul_sum _ _ _).symm
      _ ≤ (2 / (z : ℝ)) * (4 * (z : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_vonMangoldt_le z) (by positivity)
      _ = 8 := by
          have hz0 : (z : ℝ) ≠ 0 := by positivity
          field_simp
          norm_num
  have hM := abs_M4_le_one z
  have hL := (L4_bounds hz1).1
  have hprod : |L4 z * ∑ d ∈ Finset.Icc 1 z, chi4 d * Λ d / (d : ℝ)| ≤ 9 := by
    have htri := abs_sub_abs_le_abs_sub (L4 z * ∑ d ∈ Finset.Icc 1 z, chi4 d * Λ d / (d : ℝ)) (M4 z)
    rw [abs_sub_comm] at htri
    linarith
  rw [abs_mul, abs_of_pos (by linarith : 0 < L4 z)] at hprod
  have hSnn : 0 ≤ |∑ d ∈ Finset.Icc 1 z, chi4 d * Λ d / (d : ℝ)| := abs_nonneg _
  nlinarith

private lemma sum_log_div_mul_pred_le (z : ℕ) :
    ∑ m ∈ Finset.Icc 2 z, Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 8 := by
  by_cases hz : z < 2
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    norm_num
  have hz2 : 2 ≤ z := by omega
  have hterm : ∀ m ∈ Finset.Icc 2 z,
      Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) ≤
        8 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    obtain ⟨hm2, _⟩ := hm
    have hm_pos : (0 : ℝ) < m := by positivity
    have hm1_pos : (0 : ℝ) < (m - 1 : ℕ) := by exact_mod_cast (by omega : 0 < m - 1)
    have hm1_eq : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    set a := Real.sqrt ((m - 1 : ℕ) : ℝ)
    set b := Real.sqrt (m : ℝ)
    have ha_pos : 0 < a := Real.sqrt_pos.mpr hm1_pos
    have hb_pos : 0 < b := Real.sqrt_pos.mpr hm_pos
    have hab : a ≤ b := Real.sqrt_le_sqrt (by exact_mod_cast (Nat.sub_le m 1))
    have hsq_diff : b ^ 2 - a ^ 2 = 1 := by
      rw [Real.sq_sqrt hm_pos.le, Real.sq_sqrt hm1_pos.le, hm1_eq]
      ring
    have hlog : Real.log (m : ℝ) ≤ 2 * b := by
      have h1 := Real.log_le_sub_one_of_pos hb_pos
      have h2 : (m : ℝ) = b ^ 2 := (Real.sq_sqrt hm_pos.le).symm
      rw [h2, Real.log_pow]
      push_cast
      linarith
    have hdenom : (m : ℝ) * ((m : ℝ) - 1) ≥ (m : ℝ) ^ 2 / 2 := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      nlinarith
    have hstep1 : Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 4 / ((m : ℝ) * b) := by
      rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
      have hb2 : b ^ 2 = (m : ℝ) := Real.sq_sqrt hm_pos.le
      have hmb_nn : 0 ≤ (m : ℝ) * b := by positivity
      have hmul : Real.log (m : ℝ) * ((m : ℝ) * b) ≤ (2 * b) * ((m : ℝ) * b) :=
        mul_le_mul_of_nonneg_right hlog hmb_nn
      have hsqeq : (2 * b) * ((m : ℝ) * b) = 2 * (m : ℝ) ^ 2 := by
        calc (2 * b) * ((m : ℝ) * b) = 2 * (m : ℝ) * (b ^ 2) := by ring
          _ = 2 * (m : ℝ) ^ 2 := by rw [hb2]; ring
      nlinarith
    have hstep2 : 1 / (2 * (m : ℝ) * b) ≤ 1 / a - 1 / b := by
      have hdiff : 1 / a - 1 / b = 1 / (a * b * (b + a)) := by
        have hba_pos : 0 < b + a := by linarith
        field_simp
        nlinarith [hsq_diff]
      rw [hdiff]
      apply one_div_le_one_div_of_le (by positivity)
      have hb2 : b * b = (m : ℝ) := Real.mul_self_sqrt hm_pos.le
      have h1 : a * b ≤ b * b := mul_le_mul_of_nonneg_right hab hb_pos.le
      have h2 : b + a ≤ 2 * b := by linarith
      calc a * b * (b + a) ≤ (b * b) * (2 * b) :=
            mul_le_mul h1 h2 (by linarith) (by positivity)
        _ = 2 * (m : ℝ) * b := by rw [hb2]; ring
    have h8 : 4 / ((m : ℝ) * b) = 8 * (1 / (2 * (m : ℝ) * b)) := by ring
    linarith
  calc ∑ m ∈ Finset.Icc 2 z, Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1))
      ≤ ∑ m ∈ Finset.Icc 2 z,
          8 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = 8 * ∑ m ∈ Finset.Icc 2 z,
          (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ = 8 * (1 / Real.sqrt (1 : ℝ) - 1 / Real.sqrt (z : ℝ)) := by
        congr 1
        have hshift :
            ∑ m ∈ Finset.Icc 2 z, (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) =
              ∑ k ∈ Finset.Ico 1 z, (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
          refine Finset.sum_bij (fun m _ => m - 1) ?_ ?_ ?_ ?_
          · intro m hm; simp only [Finset.mem_Icc, Finset.mem_Ico] at hm ⊢; omega
          · intro a ha b hb h; simp only [Finset.mem_Icc] at ha hb; omega
          · intro k hk; simp only [Finset.mem_Ico] at hk
            exact ⟨k + 1, by simp only [Finset.mem_Icc]; omega, Nat.add_sub_cancel k 1⟩
          · intro m hm
            simp only [Finset.mem_Icc] at hm
            rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
        rw [hshift, sum_Ico_sub_succ (fun k => 1 / Real.sqrt (k : ℝ)) (by omega : 1 ≤ z)]
        simp
    _ ≤ 8 := by
        have hnn : 0 ≤ 1 / Real.sqrt (z : ℝ) := by positivity
        rw [Real.sqrt_one, div_one]
        linarith

private lemma sum_vonMangoldt_not_prime_div_le (z : ℕ) :
    ∑ d ∈ (Finset.Icc 1 z).filter (fun d => ¬ d.Prime), Λ d / (d : ℝ) ≤ 8 := by
  set S := (Finset.Icc 1 z).filter (fun d => ¬ d.Prime ∧ IsPrimePow d)
  have hS : ∑ d ∈ (Finset.Icc 1 z).filter (fun d => ¬ d.Prime), Λ d / (d : ℝ) =
      ∑ d ∈ S, Λ d / (d : ℝ) := by
    symm
    refine Finset.sum_subset (fun d hd => by
      simp only [S, Finset.mem_filter] at hd ⊢; exact ⟨hd.1, hd.2.1⟩) ?_
    intro d hd hnot
    simp only [S, Finset.mem_filter] at hd hnot
    have hnp : ¬ IsPrimePow d := fun h => hnot ⟨hd.1, hd.2, h⟩
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp, zero_div]
  rw [hS]
  have hmaps : ∀ d ∈ S, d.minFac ∈ (Finset.Icc 2 z).filter Nat.Prime := by
    intro d hd
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hd ⊢
    obtain ⟨⟨_, hdz⟩, _, hpp⟩ := hd
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff d).mp hpp
    rw [Nat.pow_minFac hk.ne', hp.minFac_eq]
    have hpz : p ≤ z := le_trans (Nat.le_self_pow hk.ne' p) hdz
    exact ⟨⟨hp.two_le, hpz⟩, hp⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ p ∈ (Finset.Icc 2 z).filter Nat.Prime,
      ∑ d ∈ S.filter (fun d => d.minFac = p), Λ d / (d : ℝ) ≤
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
    have hsub : S.filter (fun d => d.minFac = p) ⊆
        (Finset.Icc 2 (Nat.log p z + 2)).image (fun k => p ^ k) := by
      intro d hd
      simp only [S, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image] at hd ⊢
      obtain ⟨⟨⟨_, hdz⟩, hnp, hpp⟩, hmin⟩ := hd
      obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff d).mp hpp
      have hqp : q = p := by
        rw [Nat.pow_minFac hk.ne', hq.minFac_eq] at hmin; exact hmin
      rcases hqp with rfl
      have hk2 : 2 ≤ k := by
        by_contra hlt
        have hk1 : k = 1 := by omega
        subst hk1; exact hnp (by simpa using hpPrime)
      have hkle : k ≤ Nat.log q z := Nat.le_log_of_pow_le hpPrime.one_lt hdz
      exact ⟨k, ⟨hk2, by omega⟩, rfl⟩
    have h1 : ∑ d ∈ S.filter (fun d => d.minFac = p), Λ d / (d : ℝ) ≤
        ∑ d ∈ (Finset.Icc 2 (Nat.log p z + 2)).image (fun k => p ^ k),
          Real.log (p : ℝ) / (d : ℝ) := by
      calc ∑ d ∈ S.filter (fun d => d.minFac = p), Λ d / (d : ℝ)
          = ∑ d ∈ S.filter (fun d => d.minFac = p), Real.log (p : ℝ) / (d : ℝ) := by
            refine Finset.sum_congr rfl fun d hd => ?_
            simp only [S, Finset.mem_filter] at hd
            rw [ArithmeticFunction.vonMangoldt_apply, if_pos hd.1.2.2, hd.2]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
            div_nonneg (Real.log_nonneg (by exact_mod_cast hpPrime.one_lt.le)) (by positivity)
    have hinj : Set.InjOn (fun k : ℕ => p ^ k) ↑(Finset.Icc 2 (Nat.log p z + 2)) :=
      fun _ _ _ _ h => Nat.pow_right_injective hpPrime.two_le h
    rw [Finset.sum_image (fun a ha b hb h => hinj ha hb h)] at h1
    refine h1.trans ?_
    have hr_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
    have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
    have hr_lt1 : (1 : ℝ) / (p : ℝ) < 1 := (div_lt_one hr_pos).mpr hp_gt1
    have hshift :
        ∑ k ∈ Finset.Icc 2 (Nat.log p z + 2), Real.log (p : ℝ) / ((p ^ k : ℕ) : ℝ) =
          (Real.log (p : ℝ) / ((p : ℝ) ^ 2)) *
            ∑ j ∈ Finset.range (Nat.log p z + 1), ((1 : ℝ) / (p : ℝ)) ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun k _ => k - 2) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
      · intro a ha b hb h; simp only [Finset.mem_Icc] at ha hb; omega
      · intro j hj; simp only [Finset.mem_range] at hj
        exact ⟨j + 2, by simp only [Finset.mem_Icc]; omega, by omega⟩
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        rw [Nat.cast_pow, one_div_pow, div_mul_div_comm, mul_one, ← pow_add,
          show 2 + (k - 2) = k by omega]
    rw [hshift, geom_sum_eq hr_lt1.ne]
    have hflip :
        (((1 : ℝ) / (p : ℝ)) ^ (Nat.log p z + 1) - 1) / ((1 : ℝ) / (p : ℝ) - 1) =
          (1 - ((1 : ℝ) / (p : ℝ)) ^ (Nat.log p z + 1)) / (1 - (1 : ℝ) / (p : ℝ)) := by
      rw [← neg_div_neg_eq]; ring_nf
    rw [hflip]
    have hgeom : (1 - ((1 : ℝ) / (p : ℝ)) ^ (Nat.log p z + 1)) / (1 - (1 : ℝ) / (p : ℝ)) ≤
        1 / (1 - (1 : ℝ) / (p : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      have : (0 : ℝ) ≤ ((1 : ℝ) / (p : ℝ)) ^ (Nat.log p z + 1) := by positivity
      linarith
    calc (Real.log (p : ℝ) / ((p : ℝ) ^ 2)) *
            ((1 - ((1 : ℝ) / (p : ℝ)) ^ (Nat.log p z + 1)) / (1 - (1 : ℝ) / (p : ℝ)))
        ≤ (Real.log (p : ℝ) / ((p : ℝ) ^ 2)) * (1 / (1 - (1 : ℝ) / (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hgeom
            (div_nonneg (Real.log_nonneg hp_gt1.le) (by positivity))
      _ = Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
          have hp0 : (p : ℝ) ≠ 0 := hr_pos.ne'
          have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
          field_simp
  calc ∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,
          ∑ d ∈ S.filter (fun d => d.minFac = p), Λ d / (d : ℝ)
      ≤ ∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,
          Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := Finset.sum_le_sum hfiber
    _ ≤ ∑ m ∈ Finset.Icc 2 z, Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun m hm _ => ?_
        simp only [Finset.mem_Icc] at hm
        have : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
        exact div_nonneg (Real.log_nonneg (by linarith)) (by nlinarith)
    _ ≤ 8 := sum_log_div_mul_pred_le z

private noncomputable def T4 (z : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, chi4 p * Real.log (p : ℝ) / (p : ℝ)

private lemma abs_T4_le (z : ℕ) : |T4 z| ≤ 22 := by
  have hsplit :
      ∑ d ∈ Finset.Icc 1 z, chi4 d * Λ d / (d : ℝ) =
        T4 z + ∑ d ∈ (Finset.Icc 1 z).filter (fun d => ¬ d.Prime), chi4 d * Λ d / (d : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 z) Nat.Prime]
    congr 1
    unfold T4
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  have h1 := abs_sum_chi4_vonMangoldt_div_le z
  have h2 : |∑ d ∈ (Finset.Icc 1 z).filter (fun d => ¬ d.Prime), chi4 d * Λ d / (d : ℝ)| ≤ 8 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ d ∈ (Finset.Icc 1 z).filter (fun d => ¬ d.Prime), |chi4 d * Λ d / (d : ℝ)|
        ≤ ∑ d ∈ (Finset.Icc 1 z).filter (fun d => ¬ d.Prime), Λ d / (d : ℝ) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
          rw [abs_div, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
            abs_of_pos (by positivity : (0 : ℝ) < d)]
          have := abs_chi4_le_one d
          have hnn : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
          rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < d)]
          nlinarith
      _ ≤ 8 := sum_vonMangoldt_not_prime_div_le z
  have hT : T4 z = (∑ d ∈ Finset.Icc 1 z, chi4 d * Λ d / (d : ℝ)) -
      ∑ d ∈ (Finset.Icc 1 z).filter (fun d => ¬ d.Prime), chi4 d * Λ d / (d : ℝ) := by linarith
  rw [hT]
  calc |(∑ d ∈ Finset.Icc 1 z, chi4 d * Λ d / (d : ℝ)) -
          ∑ d ∈ (Finset.Icc 1 z).filter (fun d => ¬ d.Prime), chi4 d * Λ d / (d : ℝ)|
      ≤ |∑ d ∈ Finset.Icc 1 z, chi4 d * Λ d / (d : ℝ)| +
          |∑ d ∈ (Finset.Icc 1 z).filter (fun d => ¬ d.Prime), chi4 d * Λ d / (d : ℝ)| :=
        abs_sub _ _
    _ ≤ 14 + 8 := add_le_add h1 h2
    _ = 22 := by norm_num

/-- Discrete summation by parts on `Icc a b` for `1 ≤ a ≤ b`. -/
private lemma sum_by_parts (F w : ℕ → ℝ) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ k ∈ Finset.Icc a b, (F k - F (k - 1)) * w k =
      F b * w b - F (a - 1) * w a + ∑ k ∈ Finset.Ico a b, F k * (w k - w (k + 1)) := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases h : a = b + 1
    · subst h
      simp only [Finset.Icc_self, Finset.sum_singleton, Finset.Ico_self, Finset.sum_empty,
        add_zero, Nat.add_sub_cancel]
      ring
    · have hab' : a ≤ b := by omega
      have hIcc : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp), ih hab',
        Finset.sum_Ico_succ_top hab', Nat.add_sub_cancel]
      ring

private lemma abs_sum_chi4_primes_div_le (z : ℕ) :
    |∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, chi4 p / (p : ℝ)| ≤ 22 := by
  by_cases hz : z < 3
  · have hzero : ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, chi4 p / (p : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      have hp2 : p = 2 := by
        have := hp.2.two_le; omega
      subst hp2
      simp [chi4_two]
    rw [hzero, abs_zero]
    norm_num
  have hz3 : 3 ≤ z := by omega
  have hdrop :
      ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, chi4 p / (p : ℝ) =
        ∑ k ∈ Finset.Icc 3 z, (T4 k - T4 (k - 1)) * (1 / Real.log (k : ℝ)) := by
    have hleft :
        ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, chi4 p / (p : ℝ) =
          ∑ k ∈ Finset.Icc 3 z, if k.Prime then chi4 k / (k : ℝ) else 0 := by
      rw [← Finset.sum_filter]
      symm
      refine Finset.sum_subset (fun k hk => by
        simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢; exact ⟨⟨by omega, hk.1.2⟩, hk.2⟩) ?_
      intro p hp hnot
      simp only [Finset.mem_filter, Finset.mem_Icc, not_and] at hp hnot
      have hlt3 : ¬ (3 ≤ p ∧ p ≤ z) := fun h => hnot h hp.2
      have hp2 : p = 2 := by
        have := hp.2.two_le; omega
      subst hp2
      simp [chi4_two]
    rw [hleft]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    have hTdiff : T4 k - T4 (k - 1) = if k.Prime then chi4 k * Real.log (k : ℝ) / (k : ℝ) else 0 := by
      unfold T4
      have hIcc : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.filter_insert]
      split_ifs with hkp
      · rw [Finset.sum_insert (by simp; omega)]; ring
      · ring
    rw [hTdiff]
    have hlogpos : 0 < Real.log (k : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < k))
    split_ifs <;> [field_simp; simp]
  rw [hdrop, sum_by_parts T4 (fun k => 1 / Real.log (k : ℝ)) (by omega) hz3]
  have hT2 : T4 2 = 0 := by
    unfold T4
    refine Finset.sum_eq_zero fun p hp => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    have hp2 : p = 2 := by have := hp.2.two_le; omega
    subst hp2; simp [chi4_two]
  rw [show (3 - 1 : ℕ) = 2 by rfl, hT2, zero_mul, sub_zero]
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have h1 : |T4 z * (1 / Real.log (z : ℝ))| ≤ 22 / Real.log (z : ℝ) := by
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hlogz), mul_one_div]
    exact div_le_div_of_nonneg_right (abs_T4_le z) hlogz.le
  have h2 : |∑ k ∈ Finset.Ico 3 z, T4 k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ))| ≤
      22 * (1 / Real.log (3 : ℝ) - 1 / Real.log (z : ℝ)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.Ico 3 z, |T4 k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ))|
        ≤ ∑ k ∈ Finset.Ico 3 z, 22 * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          simp only [Finset.mem_Ico] at hk
          have hlk : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
          have hdiff_nn : 0 ≤ 1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ) := by
            have hle : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
              Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast Nat.le_succ k)
            linarith [one_div_le_one_div_of_le hlk hle]
          rw [abs_mul, abs_of_nonneg hdiff_nn]
          exact mul_le_mul_of_nonneg_right (abs_T4_le k) hdiff_nn
      _ = 22 * ∑ k ∈ Finset.Ico 3 z, (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) :=
          (Finset.mul_sum _ _ _).symm
      _ = 22 * (1 / Real.log (3 : ℝ) - 1 / Real.log (z : ℝ)) := by
          congr 1
          have := sum_Ico_sub_succ (fun k => 1 / Real.log (k : ℝ)) hz3
          simpa only [Nat.cast_ofNat] using this
  calc |T4 z * (1 / Real.log (z : ℝ)) +
          ∑ k ∈ Finset.Ico 3 z, T4 k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ))|
      ≤ |T4 z * (1 / Real.log (z : ℝ))| +
          |∑ k ∈ Finset.Ico 3 z, T4 k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ))| :=
        abs_add_le _ _
    _ ≤ 22 / Real.log (z : ℝ) + 22 * (1 / Real.log (3 : ℝ) - 1 / Real.log (z : ℝ)) :=
        add_le_add h1 h2
    _ = 22 / Real.log (3 : ℝ) := by ring
    _ ≤ 22 := by
        rw [div_le_iff₀ (by linarith [one_lt_log_three])]
        linarith [one_lt_log_three]

/-- Mertens' first sum `U(z) = ∑_{p ≤ z} log p / p`. -/
private noncomputable def Usum (z : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)

private lemma Usum_le (z : ℕ) (hz : 1 ≤ z) : Usum z ≤ Real.log (z : ℝ) + 2 := by
  have hlog_sum :
      ∑ n ∈ Finset.Icc 1 z, Real.log (n : ℝ) =
        ∑ d ∈ Finset.Icc 1 z, Λ d * ((z / d : ℕ) : ℝ) := by
    have hstep :
        ∑ n ∈ Finset.Icc 1 z, Real.log (n : ℝ) =
          ∑ n ∈ Finset.Icc 1 z, ∑ d ∈ n.divisors, Λ d := by
      refine Finset.sum_congr rfl fun n _ => (ArithmeticFunction.vonMangoldt_sum).symm
    rw [hstep]
    have hrhs :
        ∑ d ∈ Finset.Icc 1 z, Λ d * ((z / d : ℕ) : ℝ) =
          ∑ d ∈ Finset.Icc 1 z, ∑ _m ∈ Finset.Icc 1 (z / d), Λ d := by
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]; simp
    rw [hrhs, Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij (fun p _ => ⟨p.2, p.1 / p.2⟩) ?_ ?_ ?_ ?_
    · intro ⟨n, d⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp ⊢
      obtain ⟨⟨hn1, hnz⟩, ⟨hdn, hn0⟩⟩ := hp
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdn (by omega), le_trans (Nat.le_of_dvd (by omega) hdn) hnz⟩,
        ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdn) (Nat.pos_of_dvd_of_pos hdn (by omega)),
          Nat.div_le_div_right hnz⟩⟩
    · intro ⟨n₁, d₁⟩ hp₁ ⟨n₂, d₂⟩ hp₂ heq
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
      obtain ⟨rfl, hdiv⟩ := heq
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hp₁ hp₂
      have : n₁ = n₂ := by
        rw [← Nat.mul_div_cancel' hp₁.2.1, ← Nat.mul_div_cancel' hp₂.2.1, hdiv]
      subst this; rfl
    · intro ⟨d, m⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
      obtain ⟨⟨hd1, hdz⟩, ⟨hm1, hmz⟩⟩ := hp
      refine ⟨⟨d * m, d⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
        exact ⟨⟨Nat.mul_pos hd1 hm1, le_trans (Nat.mul_le_mul_left d hmz) (Nat.mul_div_le z d)⟩,
          ⟨dvd_mul_right d m, (Nat.mul_pos hd1 hm1).ne'⟩⟩
      · simp [Nat.mul_div_cancel_left m (by omega : 0 < d)]
    · intro _ _; rfl
  have hup : ∑ n ∈ Finset.Icc 1 z, Real.log (n : ℝ) ≤ (z : ℝ) * Real.log (z : ℝ) := by
    calc ∑ n ∈ Finset.Icc 1 z, Real.log (n : ℝ)
        ≤ ∑ _n ∈ Finset.Icc 1 z, Real.log (z : ℝ) :=
          Finset.sum_le_sum fun n hn => by
            simp only [Finset.mem_Icc] at hn
            exact Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)
      _ = (z : ℝ) * Real.log (z : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; simp
  have hlow : (z : ℝ) * Usum z - 2 * (z : ℝ) ≤ ∑ d ∈ Finset.Icc 1 z, Λ d * ((z / d : ℕ) : ℝ) := by
    have hsub : ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Λ p * ((z / p : ℕ) : ℝ) ≤
        ∑ d ∈ Finset.Icc 1 z, Λ d * ((z / d : ℕ) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    have hprime :
        (z : ℝ) * Usum z - ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Real.log (p : ℝ) ≤
          ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Λ p * ((z / p : ℕ) : ℝ) := by
      unfold Usum
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun p hp => ?_
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      rw [ArithmeticFunction.vonMangoldt_apply_prime hpPrime]
      have hdiv_ge : (z : ℝ) / (p : ℝ) - 1 ≤ ((z / p : ℕ) : ℝ) := by
        have hlt : z < p * (z / p + 1) := by
          have := Nat.div_add_mod z p
          have := Nat.mod_lt z hpPrime.pos
          nlinarith
        have hltR : (z : ℝ) ≤ (p : ℝ) * (((z / p : ℕ) : ℝ) + 1) := by exact_mod_cast hlt.le
        rw [sub_le_iff_le_add, div_le_iff₀ (by exact_mod_cast hpPrime.pos : (0 : ℝ) < p)]
        linarith
      have hlognn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpPrime.one_lt.le)
      calc (z : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) - Real.log (p : ℝ)
          = Real.log (p : ℝ) * ((z : ℝ) / (p : ℝ) - 1) := by ring
        _ ≤ Real.log (p : ℝ) * ((z / p : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hdiv_ge hlognn
    have hprim := sum_log_primes_le z
    linarith
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz
  nlinarith

private lemma sum_primes_inv_le {z : ℕ} (hz : 3 ≤ z) :
    ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      Real.log (Real.log (z : ℝ)) + 4 := by
  have hsplit2 :
      ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) =
        (1 : ℝ) / 2 + ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
    have hset : (Finset.Icc 1 z).filter Nat.Prime =
        insert 2 ((Finset.Icc 3 z).filter Nat.Prime) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
      constructor
      · rintro ⟨⟨_, hpz⟩, hp⟩
        by_cases hp2 : p = 2
        · left; exact hp2
        · right; exact ⟨⟨by have := hp.two_le; omega, hpz⟩, hp⟩
      · rintro (rfl | ⟨⟨hp3, hpz⟩, hp⟩)
        · exact ⟨⟨by omega, by omega⟩, Nat.prime_two⟩
        · exact ⟨⟨by omega, hpz⟩, hp⟩
    rw [hset, Finset.sum_insert (by simp)]
    norm_num
  rw [hsplit2]
  have hrew :
      ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) =
        ∑ k ∈ Finset.Icc 3 z, (Usum k - Usum (k - 1)) * (1 / Real.log (k : ℝ)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    have hUdiff : Usum k - Usum (k - 1) = if k.Prime then Real.log (k : ℝ) / (k : ℝ) else 0 := by
      unfold Usum
      have hIcc : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.filter_insert]
      split_ifs with hkp
      · rw [Finset.sum_insert (by simp; omega)]; ring
      · ring
    rw [hUdiff]
    have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
    split_ifs <;> [field_simp; simp]
  rw [hrew, sum_by_parts Usum (fun k => 1 / Real.log (k : ℝ)) (by omega) hz]
  have hU2_nn : 0 ≤ Usum 2 :=
    Finset.sum_nonneg fun p hp =>
      div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le))
        (by positivity)
  have hlog3 : 1 < Real.log (3 : ℝ) := one_lt_log_three
  have hlogz : 1 < Real.log (z : ℝ) :=
    lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) (by exact_mod_cast hz))
  have hterm1 : Usum z * (1 / Real.log (z : ℝ)) ≤ 1 + 2 / Real.log (z : ℝ) := by
    have hU := Usum_le z (by omega)
    have : (Real.log (z : ℝ) + 2) * (1 / Real.log (z : ℝ)) = 1 + 2 / Real.log (z : ℝ) := by
      field_simp
    calc Usum z * (1 / Real.log (z : ℝ))
        ≤ (Real.log (z : ℝ) + 2) * (1 / Real.log (z : ℝ)) :=
          mul_le_mul_of_nonneg_right hU (by positivity)
      _ = 1 + 2 / Real.log (z : ℝ) := this
  have hterm2 :
      ∑ k ∈ Finset.Ico 3 z, Usum k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤
        Real.log (Real.log (z : ℝ)) + 2 * (1 / Real.log (3 : ℝ) - 1 / Real.log (z : ℝ)) := by
    have hstep :
        ∑ k ∈ Finset.Ico 3 z, Usum k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤
          ∑ k ∈ Finset.Ico 3 z,
            ((Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))) +
              2 * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ))) := by
      refine Finset.sum_le_sum fun k hk => ?_
      simp only [Finset.mem_Ico] at hk
      have hlk : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
      have hlk1 : 0 < Real.log ((k + 1 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < k + 1))
      have hle : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast Nat.le_succ k)
      have hdiff_nn : 0 ≤ 1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ) := by
        linarith [one_div_le_one_div_of_le hlk hle]
      have hU := Usum_le k (by omega)
      have hmul : Usum k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤
          (Real.log (k : ℝ) + 2) * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hU hdiff_nn
      have hloglog :
          Real.log (k : ℝ) * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤
            Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ)) := by
        have h1 : Real.log (k : ℝ) * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) =
            1 - (Real.log ((k + 1 : ℕ) : ℝ) / Real.log (k : ℝ))⁻¹ := by
          field_simp
        rw [h1, ← Real.log_div hlk1.ne' hlk.ne']
        exact Real.one_sub_inv_le_log_of_pos (div_pos hlk1 hlk)
      linarith
    refine hstep.trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have htele1 :
        ∑ k ∈ Finset.Ico 3 z,
          (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))) =
          Real.log (Real.log (z : ℝ)) - Real.log (Real.log (3 : ℝ)) := by
      simpa only [Nat.cast_ofNat] using sum_Ico_succ_sub (fun k => Real.log (Real.log (k : ℝ))) hz
    have htele2 :
        ∑ k ∈ Finset.Ico 3 z, (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) =
          1 / Real.log (3 : ℝ) - 1 / Real.log (z : ℝ) := by
      simpa only [Nat.cast_ofNat] using sum_Ico_sub_succ (fun k => 1 / Real.log (k : ℝ)) hz
    rw [htele1, htele2]
    have hll3 : 0 ≤ Real.log (Real.log (3 : ℝ)) := Real.log_nonneg hlog3.le
    linarith
  have hU2_term : 0 ≤ Usum (3 - 1) * (1 / Real.log (3 : ℝ)) := by
    rw [show (3 - 1 : ℕ) = 2 by rfl]
    exact mul_nonneg hU2_nn (by positivity)
  have h2log3 : 2 / Real.log (3 : ℝ) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hcancel :
      2 / Real.log (z : ℝ) + 2 * (1 / Real.log (3 : ℝ) - 1 / Real.log (z : ℝ)) =
        2 / Real.log (3 : ℝ) := by ring
  simp only [Nat.cast_ofNat]
  linarith

private lemma sum_primes_mod4_eq1_inv_le {z : ℕ} (hz : 3 ≤ z) :
    ∑ p ∈ (Finset.Icc 1 z).filter (fun p => p.Prime ∧ p % 4 = 1), (1 : ℝ) / (p : ℝ) ≤
      (1 / 2) * Real.log (Real.log (z : ℝ)) + 13 := by
  have h2mul :
      2 * ∑ p ∈ (Finset.Icc 1 z).filter (fun p => p.Prime ∧ p % 4 = 1), (1 : ℝ) / (p : ℝ) ≤
        ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) +
          ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, chi4 p / (p : ℝ) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    have hsub : (Finset.Icc 1 z).filter (fun p => p.Prime ∧ p % 4 = 1) ⊆
        (Finset.Icc 1 z).filter Nat.Prime := fun p hp => by
      simp only [Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩
    calc ∑ p ∈ (Finset.Icc 1 z).filter (fun p => p.Prime ∧ p % 4 = 1), 2 * ((1 : ℝ) / (p : ℝ))
        = ∑ p ∈ (Finset.Icc 1 z).filter (fun p => p.Prime ∧ p % 4 = 1),
            ((1 : ℝ) / (p : ℝ) + chi4 p / (p : ℝ)) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          have hp4 : p % 4 = 1 := (Finset.mem_filter.mp hp).2.2
          have hchi : chi4 p = 1 := by simp [chi4, hp4]
          rw [hchi]; ring
      _ ≤ ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, ((1 : ℝ) / (p : ℝ) + chi4 p / (p : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
          have h1 : -1 ≤ chi4 p := (abs_le.mp (abs_chi4_le_one p)).1
          have hppos : (0 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.pos
          rw [← add_div]
          exact div_nonneg (by linarith) hppos.le
  have h1 := sum_primes_inv_le hz
  have h2 := (abs_le.mp (abs_sum_chi4_primes_div_le z)).2
  linarith

/- ### Section 2: Lower bound on Selberg's denominator `Sval z` -/

private def isP3 (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p % 4 = 3
private def isNotP3 (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p % 4 ≠ 3

private instance : DecidablePred isP3 := fun n =>
  Finset.decidableDforallFinset (s := n.primeFactors) (p := fun p _ => p % 4 = 3)

private instance : DecidablePred isNotP3 := fun n =>
  Finset.decidableDforallFinset (s := n.primeFactors) (p := fun p _ => p % 4 ≠ 3)

private def Dset (z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ isP3 d)

private noncomputable def Sval (z : ℕ) : ℝ :=
  ∑ d ∈ Dset z, (1 : ℝ) / (Nat.totient d : ℝ)

private def Aset (z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 z).filter isNotP3

private def Bset (z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 z).filter isP3

private lemma isP3_one : isP3 1 := by
  intro p hp; simp at hp

private lemma isNotP3_one : isNotP3 1 := by
  intro p hp; simp at hp

private lemma one_mem_Dset {z : ℕ} (hz : 1 ≤ z) : 1 ∈ Dset z := by
  simp only [Dset, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨le_rfl, hz⟩, squarefree_one, isP3_one⟩

private lemma Sval_ge_one {z : ℕ} (hz : 1 ≤ z) : 1 ≤ Sval z := by
  unfold Sval
  have h := Finset.single_le_sum (f := fun d => (1 : ℝ) / (Nat.totient d : ℝ))
    (fun _ _ => by positivity) (one_mem_Dset hz)
  simpa using h

private lemma Sval_pos {z : ℕ} (hz : 1 ≤ z) : 0 < Sval z :=
  lt_of_lt_of_le zero_lt_one (Sval_ge_one hz)

private lemma log_le_harmonic (z : ℕ) (hz : 1 ≤ z) :
    Real.log (z : ℝ) ≤ ∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / (n : ℝ) := by
  have h1 : Real.log ((z + 1 : ℕ) : ℝ) ≤ ∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / (n : ℝ) := by
    have htele :
        Real.log ((z + 1 : ℕ) : ℝ) =
          ∑ n ∈ Finset.Icc 1 z, (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) := by
      induction z with
      | zero => omega
      | succ k ih =>
        by_cases hk : k = 0
        · subst hk; simp; norm_num
        · have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.sum_insert (by simp), ← ih (by omega)]
          ring
    rw [htele]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [← Real.log_div hn1_pos.ne' hn_pos.ne']
    have hdiv : ((n + 1 : ℕ) : ℝ) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
      push_cast; field_simp; ring
    linarith [Real.log_le_sub_one_of_pos (div_pos hn1_pos hn_pos)]
  exact le_trans (Real.log_le_log (by exact_mod_cast hz) (by exact_mod_cast Nat.le_succ z)) h1

private lemma sum_image_le_sum {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset α)
    (g : α → β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.image g, f b ≤ ∑ a ∈ s, f (g a) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.image_insert, Finset.sum_insert ha]
    by_cases hmem : g a ∈ s.image g
    · rw [Finset.insert_eq_of_mem hmem]
      linarith [hf (g a)]
    · rw [Finset.sum_insert hmem]
      linarith

private lemma harmonic_le_A_mul_B {z : ℕ} (hz : 1 ≤ z) :
    Real.log (z : ℝ) ≤
      (∑ u ∈ Aset z, (1 : ℝ) / (u : ℝ)) * (∑ v ∈ Bset z, (1 : ℝ) / (v : ℝ)) := by
  refine (log_le_harmonic z hz).trans ?_
  have hsub : Finset.Icc 1 z ⊆ (Aset z ×ˢ Bset z).image (fun p => p.1 * p.2) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    obtain ⟨hn1, hnz⟩ := hn
    have hn0 : n ≠ 0 := by omega
    set u := ∏ p ∈ n.primeFactors.filter (fun p => p % 4 ≠ 3), p ^ (n.factorization p)
    set v := ∏ p ∈ n.primeFactors.filter (fun p => p % 4 = 3), p ^ (n.factorization p)
    have huv : u * v = n := by
      have h1 := Finset.prod_filter_mul_prod_filter_not n.primeFactors
        (fun p => p % 4 ≠ 3) (fun p => p ^ (n.factorization p))
      simp only [not_not] at h1
      rw [h1]
      exact Nat.prod_factorization_pow_eq_self hn0
    have hu_pos : 1 ≤ u := Finset.one_le_prod' fun p hp =>
      Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
    have hv_pos : 1 ≤ v := Finset.one_le_prod' fun p hp =>
      Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
    have hu_le : u ≤ z := le_trans (Nat.le_of_dvd (by omega) ⟨v, huv.symm⟩) hnz
    have hv_le : v ≤ z := le_trans (Nat.le_of_dvd (by omega) ⟨u, by rw [mul_comm]; exact huv.symm⟩) hnz
    have hu_notP3 : isNotP3 u := by
      intro q hq
      have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hqdvd : q ∣ u := Nat.dvd_of_mem_primeFactors hq
      obtain ⟨p, hp, hqp⟩ := (hqPrime.prime.dvd_finsetProd_iff _).mp hqdvd
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
      have hqp' : q ∣ p := hqPrime.prime.dvd_of_dvd_pow hqp
      have heq : q = p := (Nat.prime_dvd_prime_iff_eq hqPrime hpPrime).mp hqp'
      subst heq
      exact (Finset.mem_filter.mp hp).2
    have hv_P3 : isP3 v := by
      intro q hq
      have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hqdvd : q ∣ v := Nat.dvd_of_mem_primeFactors hq
      obtain ⟨p, hp, hqp⟩ := (hqPrime.prime.dvd_finsetProd_iff _).mp hqdvd
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
      have hqp' : q ∣ p := hqPrime.prime.dvd_of_dvd_pow hqp
      have heq : q = p := (Nat.prime_dvd_prime_iff_eq hqPrime hpPrime).mp hqp'
      subst heq
      exact (Finset.mem_filter.mp hp).2
    rw [Finset.mem_image]
    refine ⟨(u, v), Finset.mem_product.mpr ⟨?_, ?_⟩, huv⟩
    · simp only [Aset, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hu_pos, hu_le⟩, hu_notP3⟩
    · simp only [Bset, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hv_pos, hv_le⟩, hv_P3⟩
  calc ∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / (n : ℝ)
      ≤ ∑ n ∈ (Aset z ×ˢ Bset z).image (fun p : ℕ × ℕ => p.1 * p.2), (1 : ℝ) / (n : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ p ∈ Aset z ×ˢ Bset z, (1 : ℝ) / (((p.1 * p.2 : ℕ) : ℝ)) :=
        sum_image_le_sum (Aset z ×ˢ Bset z) (fun p : ℕ × ℕ => p.1 * p.2) (fun n : ℕ => (1 : ℝ) / (n : ℝ))
          fun _ => by positivity
    _ = ∑ p ∈ Aset z ×ˢ Bset z, ((1 : ℝ) / (p.1 : ℝ)) * ((1 : ℝ) / (p.2 : ℝ)) := by
        refine Finset.sum_congr rfl fun p _ => by rw [Nat.cast_mul]; ring
    _ = (∑ u ∈ Aset z, (1 : ℝ) / (u : ℝ)) * (∑ v ∈ Bset z, (1 : ℝ) / (v : ℝ)) := by
        rw [Finset.sum_product]
        dsimp only
        rw [← Finset.sum_mul_sum]

private lemma sum_inv_mul_pred_le (z : ℕ) :
    ∑ m ∈ Finset.Icc 2 z, (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 1 := by
  by_cases hz : z < 2
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; norm_num
  have hz2 : 2 ≤ z := by omega
  have hrew :
      ∑ m ∈ Finset.Icc 2 z, (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) =
        ∑ k ∈ Finset.Ico 1 z, (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
    refine Finset.sum_bij (fun m _ => m - 1) ?_ ?_ ?_ ?_
    · intro m hm; simp only [Finset.mem_Icc, Finset.mem_Ico] at hm ⊢; omega
    · intro a ha b hb h; simp only [Finset.mem_Icc] at ha hb; omega
    · intro k hk; simp only [Finset.mem_Ico] at hk
      exact ⟨k + 1, by simp only [Finset.mem_Icc]; omega, Nat.add_sub_cancel k 1⟩
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hm1_eq : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
      have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
        have : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
        linarith
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m), hm1_eq]
      field_simp
      ring
  rw [hrew, sum_Ico_sub_succ (fun k => (1 : ℝ) / (k : ℝ)) (by omega : 1 ≤ z)]
  have : 0 ≤ 1 / (z : ℝ) := by positivity
  simp only [Nat.cast_one, div_one]
  linarith

private lemma sum_Aset_le {z : ℕ} (hz : 3 ≤ z) :
    ∑ u ∈ Aset z, (1 : ℝ) / (u : ℝ) ≤ 2 * Real.exp 14 * Real.sqrt (Real.log (z : ℝ)) := by
  set P := (Finset.Icc 1 z).filter (fun p => p.Prime ∧ p % 4 ≠ 3)
  -- Step 1: Bound ∑_{u ∈ Aset z} 1/u by ∏_{p ∈ P} ∑_{e ≤ z} 1/p^e
  have h1 : ∑ u ∈ Aset z, (1 : ℝ) / (u : ℝ) ≤
      ∏ p ∈ P, ∑ e ∈ Finset.range (z + 1), (1 : ℝ) / ((p : ℝ) ^ e) := by
    rw [Finset.prod_sum]
    set g : ℕ → ∀ p ∈ P, ℕ := fun u p _ => u.factorization p
    have hprod_eq : ∀ u ∈ Aset z,
        ∏ p ∈ P.attach, (p.1 : ℕ) ^ (u.factorization p.1) = u := by
      intro u hu
      simp only [Aset, Finset.mem_filter, Finset.mem_Icc] at hu
      obtain ⟨⟨hu1, huz⟩, hunotP3⟩ := hu
      have hu0 : u ≠ 0 := by omega
      have hsub : u.primeFactors ⊆ P := by
        intro p hp
        simp only [P, Finset.mem_filter, Finset.mem_Icc]
        have hpPrime := Nat.prime_of_mem_primeFactors hp
        have hple := le_trans (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)) huz
        exact ⟨⟨hpPrime.one_lt.le, hple⟩, hpPrime, hunotP3 p hp⟩
      rw [Finset.prod_attach P (fun p => p ^ (u.factorization p))]
      have hfilt : ∏ p ∈ P, p ^ (u.factorization p) =
          ∏ p ∈ u.primeFactors, p ^ (u.factorization p) := by
        symm
        refine Finset.prod_subset hsub fun p _ hpnot => ?_
        have hzero : u.factorization p = 0 := by
          by_contra hne
          have hmem_pf : p ∈ u.primeFactors := by
            rw [← Nat.support_factorization]
            exact Finsupp.mem_support_iff.mpr hne
          exact hpnot hmem_pf
        rw [hzero, pow_zero]
      rw [hfilt]
      exact Nat.prod_factorization_pow_eq_self hu0
    have hinj : Set.InjOn g ↑(Aset z) := by
      intro u₁ hu₁ u₂ hu₂ h
      have h1' := hprod_eq u₁ hu₁
      have h2' := hprod_eq u₂ hu₂
      rw [← h1', ← h2']
      refine Finset.prod_congr rfl fun p _ => ?_
      have := congrFun (congrFun h p.1) p.2
      simp only [g] at this
      rw [this]
    have hmem : ∀ u ∈ Aset z, g u ∈ P.pi (fun _ => Finset.range (z + 1)) := by
      intro u hu
      rw [Finset.mem_pi]
      intro p hp
      rw [Finset.mem_range]
      simp only [Aset, Finset.mem_filter, Finset.mem_Icc] at hu
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2.1
      have hpow_le : p ^ (u.factorization p) ≤ u :=
        Nat.le_of_dvd (by omega) (Nat.ordProj_dvd u p)
      have hlt : u.factorization p < p ^ (u.factorization p) :=
        Nat.lt_pow_self hpPrime.one_lt
      dsimp only [g]
      omega
    have hval : ∀ u ∈ Aset z,
        (1 : ℝ) / (u : ℝ) = ∏ p ∈ P.attach, (1 : ℝ) / ((p.1 : ℝ) ^ (g u p.1 p.2)) := by
      intro u hu
      have hpe := hprod_eq u hu
      conv_lhs => rw [← hpe]
      rw [Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun p _ => by simp only [g, Nat.cast_pow, one_div]
    calc ∑ u ∈ Aset z, (1 : ℝ) / (u : ℝ)
        = ∑ u ∈ Aset z, ∏ p ∈ P.attach, (1 : ℝ) / ((p.1 : ℝ) ^ (g u p.1 p.2)) :=
          Finset.sum_congr rfl hval
      _ = ∑ f ∈ (Aset z).image g, ∏ p ∈ P.attach, (1 : ℝ) / ((p.1 : ℝ) ^ (f p.1 p.2)) := by
          symm; exact Finset.sum_image (fun a ha b hb h => hinj ha hb h)
      _ ≤ ∑ f ∈ P.pi (fun _ => Finset.range (z + 1)),
            ∏ p ∈ P.attach, (1 : ℝ) / ((p.1 : ℝ) ^ (f p.1 p.2)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ =>
            Finset.prod_nonneg fun _ _ => by positivity
          intro f hf
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hf
          exact hmem u hu
  -- Step 2: Geometric series bound on each factor
  have h2 : ∏ p ∈ P, ∑ e ∈ Finset.range (z + 1), (1 : ℝ) / ((p : ℝ) ^ e) ≤
      ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ))⁻¹ := by
    refine Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) fun p hp => ?_
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
    have hr_lt1 : (1 : ℝ) / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr hp_gt1
    have hrew : ∑ e ∈ Finset.range (z + 1), (1 : ℝ) / ((p : ℝ) ^ e) =
        ∑ e ∈ Finset.range (z + 1), ((1 : ℝ) / (p : ℝ)) ^ e :=
      Finset.sum_congr rfl fun e _ => by rw [one_div_pow]
    rw [hrew, geom_sum_eq hr_lt1.ne, inv_eq_one_div]
    have hflip :
        (((1 : ℝ) / (p : ℝ)) ^ (z + 1) - 1) / ((1 : ℝ) / (p : ℝ) - 1) =
          (1 - ((1 : ℝ) / (p : ℝ)) ^ (z + 1)) / (1 - (1 : ℝ) / (p : ℝ)) := by
      rw [← neg_div_neg_eq]; ring_nf
    rw [hflip]
    apply div_le_div_of_nonneg_right _ (by linarith)
    have : (0 : ℝ) ≤ ((1 : ℝ) / (p : ℝ)) ^ (z + 1) := by positivity
    linarith
  -- Step 3: Split off p = 2 and bound the remaining primes ≡ 1 (mod 4) by exp
  have h2mem : 2 ∈ P := by
    simp only [P, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, Nat.prime_two, by decide⟩
  have hP1 : P.erase 2 = (Finset.Icc 1 z).filter (fun p => p.Prime ∧ p % 4 = 1) := by
    ext p
    simp only [P, Finset.mem_erase, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hp2, ⟨hI, hp, hne3⟩⟩
      refine ⟨hI, hp, ?_⟩
      have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
      omega
    · rintro ⟨hI, hp, heq1⟩
      exact ⟨by omega, ⟨hI, hp, by omega⟩⟩
  have h3 : ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ))⁻¹ ≤
      2 * Real.exp 14 * Real.sqrt (Real.log (z : ℝ)) := by
    rw [← Finset.mul_prod_erase P _ h2mem, hP1]
    have h2val : (1 - (1 : ℝ) / ((2 : ℕ) : ℝ))⁻¹ = 2 := by norm_num
    rw [h2val]
    have hprod_exp :
        ∏ p ∈ (Finset.Icc 1 z).filter (fun p => p.Prime ∧ p % 4 = 1),
          (1 - (1 : ℝ) / (p : ℝ))⁻¹ ≤
        Real.exp (∑ p ∈ (Finset.Icc 1 z).filter (fun p => p.Prime ∧ p % 4 = 1),
          ((1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))) := by
      rw [Real.exp_sum]
      refine Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_
      · have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_lt
        have : (1 : ℝ) / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr hp1
        exact inv_nonneg.mpr (by linarith)
      · have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2.1
        have hp1 : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
        have hp0 : (p : ℝ) ≠ 0 := by linarith
        have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
        have hident : (1 - (1 : ℝ) / (p : ℝ))⁻¹ =
            ((1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + 1 := by
          field_simp
          ring
        rw [hident]
        exact Real.add_one_le_exp _
    have hsum_bound :
        ∑ p ∈ (Finset.Icc 1 z).filter (fun p => p.Prime ∧ p % 4 = 1),
          ((1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        (1 / 2) * Real.log (Real.log (z : ℝ)) + 14 := by
      rw [Finset.sum_add_distrib]
      have ha := sum_primes_mod4_eq1_inv_le hz
      have hb :
          ∑ p ∈ (Finset.Icc 1 z).filter (fun p => p.Prime ∧ p % 4 = 1),
            (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
        calc ∑ p ∈ (Finset.Icc 1 z).filter (fun p => p.Prime ∧ p % 4 = 1),
              (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
            ≤ ∑ m ∈ Finset.Icc 2 z, (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun m hm _ => ?_
              · simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
                exact ⟨hp.2.1.two_le, hp.1.2⟩
              · simp only [Finset.mem_Icc] at hm
                have : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
                exact div_nonneg zero_le_one (by nlinarith)
          _ ≤ 1 := sum_inv_mul_pred_le z
      linarith
    have hlogz : 0 < Real.log (z : ℝ) :=
      lt_trans zero_lt_one (lt_of_lt_of_le one_lt_log_three
        (Real.log_le_log (by norm_num) (by exact_mod_cast hz)))
    have hexp_sqrt :
        Real.exp ((1 / 2) * Real.log (Real.log (z : ℝ)) + 14) =
          Real.exp 14 * Real.sqrt (Real.log (z : ℝ)) := by
      rw [Real.exp_add, mul_comm]
      congr 1
      have hsq : (Real.exp ((1 / 2) * Real.log (Real.log (z : ℝ)))) ^ 2 = Real.log (z : ℝ) := by
        rw [← Real.exp_nat_mul]
        have : (2 : ℕ) * ((1 / 2 : ℝ) * Real.log (Real.log (z : ℝ))) = Real.log (Real.log (z : ℝ)) := by
          push_cast; ring
        rw [this, Real.exp_log hlogz]
      conv_rhs => rw [← hsq]
      rw [Real.sqrt_sq (Real.exp_pos _).le]
    calc 2 * ∏ p ∈ (Finset.Icc 1 z).filter (fun p => p.Prime ∧ p % 4 = 1),
              (1 - (1 : ℝ) / (p : ℝ))⁻¹
        ≤ 2 * Real.exp ((1 / 2) * Real.log (Real.log (z : ℝ)) + 14) := by
          exact mul_le_mul_of_nonneg_left
            (hprod_exp.trans (Real.exp_le_exp.mpr hsum_bound)) (by norm_num)
      _ = 2 * Real.exp 14 * Real.sqrt (Real.log (z : ℝ)) := by rw [hexp_sqrt]; ring
  exact (h1.trans h2).trans h3

private def rad (v : ℕ) : ℕ := ∏ p ∈ v.primeFactors, p

private lemma rad_mem_Dset {z v : ℕ} (hv : v ∈ Bset z) : rad v ∈ Dset z := by
  simp only [Bset, Dset, Finset.mem_filter, Finset.mem_Icc] at hv ⊢
  obtain ⟨⟨hv1, hvz⟩, hvP3⟩ := hv
  have hrad_pos : 1 ≤ rad v :=
    Finset.one_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hrad_le : rad v ≤ z :=
    le_trans (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd v)) hvz
  have hrad_sq : Squarefree (rad v) := by
    unfold rad
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).squarefree
    intro p hp q hq hpq
    dsimp only [Function.onFun]
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  have hrad_pf : (rad v).primeFactors = v.primeFactors := by
    unfold rad
    exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors hp
  refine ⟨⟨hrad_pos, hrad_le⟩, hrad_sq, ?_⟩
  intro p hp
  rw [hrad_pf] at hp
  exact hvP3 p hp

private lemma totient_eq_prod_sub_one_of_squarefree {d : ℕ} (hd : Squarefree d) :
    (Nat.totient d : ℝ) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
  have h1 := Nat.totient_eq_div_primeFactors_mul d
  rw [Nat.prod_primeFactors_of_squarefree hd, Nat.div_self (Nat.pos_of_ne_zero hd.ne_zero), one_mul] at h1
  rw [h1, Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
  rw [Nat.cast_sub hp1, Nat.cast_one]

private lemma sum_Bset_le_Sval (z : ℕ) :
    ∑ v ∈ Bset z, (1 : ℝ) / (v : ℝ) ≤ Sval z := by
  unfold Sval
  rw [← Finset.sum_fiberwise_of_maps_to (fun v hv => rad_mem_Dset hv)]
  refine Finset.sum_le_sum fun d hd => ?_
  have hd_sq : Squarefree d := (Finset.mem_filter.mp hd).2.1
  set F := (Bset z).filter (fun v => rad v = d)
  set P := d.primeFactors
  have h1 : ∑ v ∈ F, (1 : ℝ) / (v : ℝ) ≤
      ∏ p ∈ P, ∑ e ∈ Finset.Icc 1 z, (1 : ℝ) / ((p : ℝ) ^ e) := by
    rw [Finset.prod_sum]
    set g : ℕ → ∀ p ∈ P, ℕ := fun v p _ => v.factorization p
    have hv_pf : ∀ v ∈ F, v.primeFactors = P := by
      intro v hv
      have hrad : rad v = d := (Finset.mem_filter.mp hv).2
      have h1' : (rad v).primeFactors = v.primeFactors := by
        unfold rad
        exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors hp
      rw [← h1', hrad]
    have hprod_eq : ∀ v ∈ F, ∏ p ∈ P.attach, (p.1 : ℕ) ^ (v.factorization p.1) = v := by
      intro v hv
      have hv1 : 1 ≤ v := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1).1
      rw [Finset.prod_attach P (fun p => p ^ (v.factorization p)), ← hv_pf v hv]
      exact Nat.prod_factorization_pow_eq_self (by omega)
    have hinj : Set.InjOn g ↑F := by
      intro v₁ hv₁ v₂ hv₂ h
      rw [← hprod_eq v₁ hv₁, ← hprod_eq v₂ hv₂]
      refine Finset.prod_congr rfl fun p _ => ?_
      have := congrFun (congrFun h p.1) p.2
      simp only [g] at this
      rw [this]
    have hmem : ∀ v ∈ F, g v ∈ P.pi (fun _ => Finset.Icc 1 z) := by
      intro v hv
      rw [Finset.mem_pi]
      intro p hp
      rw [Finset.mem_Icc]
      have hv_in : v ∈ Bset z := (Finset.mem_filter.mp hv).1
      have hv1 : 1 ≤ v := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv_in).1).1
      have hvz : v ≤ z := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv_in).1).2
      have hp_v : p ∈ v.primeFactors := by rw [hv_pf v hv]; exact hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpos : 1 ≤ v.factorization p := by
        have := Finsupp.mem_support_iff.mp (Nat.support_factorization v ▸ hp_v)
        omega
      have hle : v.factorization p ≤ z := by
        have hpow_le : p ^ (v.factorization p) ≤ v :=
          Nat.le_of_dvd (by omega) (Nat.ordProj_dvd v p)
        have hlt : v.factorization p < p ^ (v.factorization p) :=
          Nat.lt_pow_self hpPrime.one_lt
        omega
      exact ⟨hpos, hle⟩
    calc ∑ v ∈ F, (1 : ℝ) / (v : ℝ)
        = ∑ v ∈ F, ∏ p ∈ P.attach, (1 : ℝ) / ((p.1 : ℝ) ^ (g v p.1 p.2)) := by
          refine Finset.sum_congr rfl fun v hv => ?_
          conv_lhs => rw [← hprod_eq v hv]
          rw [Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
          refine Finset.prod_congr rfl fun p _ => by simp only [g, Nat.cast_pow, one_div]
      _ = ∑ f ∈ F.image g, ∏ p ∈ P.attach, (1 : ℝ) / ((p.1 : ℝ) ^ (f p.1 p.2)) := by
          symm; exact Finset.sum_image (fun a ha b hb h => hinj ha hb h)
      _ ≤ ∑ f ∈ P.pi (fun _ => Finset.Icc 1 z),
            ∏ p ∈ P.attach, (1 : ℝ) / ((p.1 : ℝ) ^ (f p.1 p.2)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ =>
            Finset.prod_nonneg fun _ _ => by positivity
          intro f hf
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hf
          exact hmem v hv
  have h2 : ∏ p ∈ P, ∑ e ∈ Finset.Icc 1 z, (1 : ℝ) / ((p : ℝ) ^ e) ≤
      ∏ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) := by
    refine Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) fun p hp => ?_
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
    have hr_lt1 : (1 : ℝ) / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr hp_gt1
    have hshift :
        ∑ e ∈ Finset.Icc 1 z, (1 : ℝ) / ((p : ℝ) ^ e) =
          ((1 : ℝ) / (p : ℝ)) * ∑ j ∈ Finset.range z, ((1 : ℝ) / (p : ℝ)) ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun e _ => e - 1) ?_ ?_ ?_ ?_
      · intro e he; simp only [Finset.mem_Icc, Finset.mem_range] at he ⊢; omega
      · intro a ha b hb h; simp only [Finset.mem_Icc] at ha hb; omega
      · intro j hj; simp only [Finset.mem_range] at hj
        exact ⟨j + 1, by simp only [Finset.mem_Icc]; omega, by omega⟩
      · intro e he
        simp only [Finset.mem_Icc] at he
        rw [one_div_pow, div_mul_div_comm, mul_one, ← pow_succ', Nat.sub_add_cancel he.1]
    rw [hshift, geom_sum_eq hr_lt1.ne]
    have hflip :
        (((1 : ℝ) / (p : ℝ)) ^ z - 1) / ((1 : ℝ) / (p : ℝ) - 1) =
          (1 - ((1 : ℝ) / (p : ℝ)) ^ z) / (1 - (1 : ℝ) / (p : ℝ)) := by
      rw [← neg_div_neg_eq]; ring_nf
    rw [hflip]
    have hgeom : (1 - ((1 : ℝ) / (p : ℝ)) ^ z) / (1 - (1 : ℝ) / (p : ℝ)) ≤
        1 / (1 - (1 : ℝ) / (p : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      have : (0 : ℝ) ≤ ((1 : ℝ) / (p : ℝ)) ^ z := by positivity
      linarith
    calc ((1 : ℝ) / (p : ℝ)) * ((1 - ((1 : ℝ) / (p : ℝ)) ^ z) / (1 - (1 : ℝ) / (p : ℝ)))
        ≤ ((1 : ℝ) / (p : ℝ)) * (1 / (1 - (1 : ℝ) / (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = (1 : ℝ) / ((p : ℝ) - 1) := by
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
          field_simp
  have h3 : ∏ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) = (1 : ℝ) / (Nat.totient d : ℝ) := by
    rw [totient_eq_prod_sub_one_of_squarefree hd_sq, one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun _ _ => by rw [one_div]
  exact (h1.trans h2).trans_eq h3

private lemma Sval_lower_bound {z : ℕ} (hz : 3 ≤ z) :
    Real.sqrt (Real.log (z : ℝ)) / (2 * Real.exp 14) ≤ Sval z := by
  have hAB := harmonic_le_A_mul_B (by omega : 1 ≤ z)
  have hA := sum_Aset_le hz
  have hB := sum_Bset_le_Sval z
  have hB_nn : 0 ≤ ∑ v ∈ Bset z, (1 : ℝ) / (v : ℝ) :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hlog_pos : 0 < Real.log (z : ℝ) :=
    lt_trans zero_lt_one (lt_of_lt_of_le one_lt_log_three
      (Real.log_le_log (by norm_num) (by exact_mod_cast hz)))
  have hprod : Real.log (z : ℝ) ≤ (2 * Real.exp 14 * Real.sqrt (Real.log (z : ℝ))) * Sval z := by
    calc Real.log (z : ℝ)
        ≤ (∑ u ∈ Aset z, (1 : ℝ) / (u : ℝ)) * (∑ v ∈ Bset z, (1 : ℝ) / (v : ℝ)) := hAB
      _ ≤ (2 * Real.exp 14 * Real.sqrt (Real.log (z : ℝ))) * Sval z :=
          mul_le_mul hA hB hB_nn (by positivity)
  have hsq : Real.sqrt (Real.log (z : ℝ)) * Real.sqrt (Real.log (z : ℝ)) = Real.log (z : ℝ) :=
    Real.mul_self_sqrt hlog_pos.le
  rw [div_le_iff₀ (by positivity)]
  have hrt_pos : 0 < Real.sqrt (Real.log (z : ℝ)) := Real.sqrt_pos.mpr hlog_pos
  nlinarith

/- ### Section 3: Selberg's Λ² sieve upper bound for `isNotP3` -/

private noncomputable def selbergLam (z d : ℕ) : ℝ :=
  if d ∈ Dset z then
    ((μ d : ℝ) * (d : ℝ) / (Sval z * (Nat.totient d : ℝ))) *
      ∑ m ∈ (Dset z).filter (fun m => d * m ≤ z ∧ Nat.Coprime m d),
        (1 : ℝ) / (Nat.totient m : ℝ)
  else 0

private lemma dvd_mem_Dset {z d a : ℕ} (hd : d ∈ Dset z) (ha : a ∣ d) : a ∈ Dset z := by
  simp only [Dset, Finset.mem_filter, Finset.mem_Icc] at hd ⊢
  obtain ⟨⟨hd1, hdz⟩, hd_sq, hd_P3⟩ := hd
  have ha1 : 1 ≤ a := Nat.pos_of_dvd_of_pos ha (by omega)
  have haz : a ≤ z := le_trans (Nat.le_of_dvd (by omega) ha) hdz
  refine ⟨⟨ha1, haz⟩, hd_sq.squarefree_of_dvd ha, ?_⟩
  intro p hp
  exact hd_P3 p (Nat.primeFactors_mono ha (by omega) hp)

private lemma mul_mem_Dset {z a b : ℕ} (ha : a ∈ Dset z) (hb : b ∈ Dset z)
    (hab : a * b ≤ z) (hcop : Nat.Coprime a b) : a * b ∈ Dset z := by
  simp only [Dset, Finset.mem_filter, Finset.mem_Icc] at ha hb ⊢
  obtain ⟨⟨ha1, _⟩, ha_sq, ha_P3⟩ := ha
  obtain ⟨⟨hb1, _⟩, hb_sq, hb_P3⟩ := hb
  refine ⟨⟨Nat.mul_pos ha1 hb1, hab⟩, (Nat.squarefree_mul hcop).mpr ⟨ha_sq, hb_sq⟩, ?_⟩
  intro p hp
  rw [Nat.primeFactors_mul (by omega) (by omega), Finset.mem_union] at hp
  rcases hp with h | h
  · exact ha_P3 p h
  · exact hb_P3 p h

private lemma selbergLam_one {z : ℕ} (hz : 1 ≤ z) : selbergLam z 1 = 1 := by
  unfold selbergLam
  rw [if_pos (one_mem_Dset hz)]
  have hfilt : (Dset z).filter (fun m => 1 * m ≤ z ∧ Nat.Coprime m 1) = Dset z := by
    ext m
    simp only [Finset.mem_filter, one_mul, and_iff_left_iff_imp]
    intro hm
    exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2, Nat.coprime_one_right m⟩
  rw [hfilt, ArithmeticFunction.moebius_apply_one, Nat.totient_one, Int.cast_one, Nat.cast_one]
  change ((1 : ℝ) * (1 : ℝ) / (Sval z * (1 : ℝ))) * Sval z = 1
  have hS : Sval z ≠ 0 := (Sval_pos hz).ne'
  field_simp

private lemma div_totient_eq_sum_divisors {d : ℕ} (hd : Squarefree d) :
    (d : ℝ) / (Nat.totient d : ℝ) = ∑ a ∈ d.divisors, (1 : ℝ) / (Nat.totient a : ℝ) := by
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hphi_pos : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd_pos
  rw [div_eq_iff hphi_pos.ne', Finset.sum_mul]
  have hsum : ∑ a ∈ d.divisors, (1 : ℝ) / (Nat.totient a : ℝ) * (Nat.totient d : ℝ) =
      ∑ a ∈ d.divisors, (Nat.totient (d / a) : ℝ) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    have had : a ∣ d := Nat.dvd_of_mem_divisors ha
    have ha_pos : 0 < a := Nat.pos_of_mem_divisors ha
    have hcop : Nat.Coprime a (d / a) := by
      have hm : a * (d / a) = d := Nat.mul_div_cancel' had
      exact (Nat.squarefree_mul_iff.mp (hm.symm ▸ hd)).1
    have hmul : Nat.totient d = Nat.totient a * Nat.totient (d / a) := by
      conv_lhs => rw [← Nat.mul_div_cancel' had]
      exact Nat.totient_mul hcop
    have hpa : (Nat.totient a : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr ha_pos).ne'
    rw [hmul, Nat.cast_mul]
    field_simp
  rw [hsum, ← Nat.cast_sum, Nat.sum_div_divisors, Nat.sum_totient]

private lemma abs_selbergLam_le_one {z : ℕ} (hz : 1 ≤ z) (d : ℕ) : |selbergLam z d| ≤ 1 := by
  unfold selbergLam
  split_ifs with hd
  · have hd_sq : Squarefree d := (Finset.mem_filter.mp hd).2.1
    have hd_pos : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    have hSpos : 0 < Sval z := Sval_pos hz
    have hphipos : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd_pos
    have hmu : |(μ d : ℝ)| = 1 := by
      rw [← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree hd_sq, Int.cast_one]
    have hsum_nn : 0 ≤ ∑ m ∈ (Dset z).filter (fun m => d * m ≤ z ∧ Nat.Coprime m d),
        (1 : ℝ) / (Nat.totient m : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
    rw [abs_mul, abs_div, abs_mul, hmu, one_mul, abs_of_pos (by positivity : (0 : ℝ) < d),
      abs_of_pos (mul_pos hSpos hphipos), abs_of_nonneg hsum_nn]
    rw [show (d : ℝ) / (Sval z * (Nat.totient d : ℝ)) =
        (1 / Sval z) * ((d : ℝ) / (Nat.totient d : ℝ)) by ring, mul_assoc,
      one_div_mul_eq_div, div_le_iff₀ hSpos, one_mul, div_totient_eq_sum_divisors hd_sq]
    set M := (Dset z).filter (fun m => d * m ≤ z ∧ Nat.Coprime m d)
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    have hmem : ∀ p ∈ d.divisors ×ˢ M, p.1 * p.2 ∈ Dset z := by
      intro ⟨a, m⟩ hp
      simp only [Finset.mem_product, Nat.mem_divisors, M, Finset.mem_filter] at hp
      obtain ⟨⟨had, _⟩, ⟨hmD, hdm, hcop⟩⟩ := hp
      have haD : a ∈ Dset z := dvd_mem_Dset hd had
      have ham_le : a * m ≤ z :=
        le_trans (Nat.mul_le_mul_right m (Nat.le_of_dvd hd_pos had)) hdm
      have hcop_am : Nat.Coprime a m := (hcop.coprime_dvd_right had).symm
      exact mul_mem_Dset haD hmD ham_le hcop_am
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) ↑(d.divisors ×ˢ M) := by
      intro ⟨a₁, m₁⟩ h₁ ⟨a₂, m₂⟩ h₂ heq
      dsimp only at heq
      simp only [Finset.mem_coe, Finset.mem_product, Nat.mem_divisors, M, Finset.mem_filter] at h₁ h₂
      have hg₁ : Nat.gcd (a₁ * m₁) d = a₁ := by
        rw [Nat.Coprime.gcd_mul_right_cancel a₁ h₁.2.2.2, Nat.gcd_eq_left h₁.1.1]
      have hg₂ : Nat.gcd (a₂ * m₂) d = a₂ := by
        rw [Nat.Coprime.gcd_mul_right_cancel a₂ h₂.2.2.2, Nat.gcd_eq_left h₂.1.1]
      have ha : a₁ = a₂ := by rw [← hg₁, ← hg₂, heq]
      subst ha
      have ha_pos : 0 < a₁ := Nat.pos_of_dvd_of_pos h₁.1.1 hd_pos
      have hm : m₁ = m₂ := Nat.eq_of_mul_eq_mul_left ha_pos heq
      subst hm; rfl
    calc ∑ p ∈ d.divisors ×ˢ M, (1 : ℝ) / (Nat.totient p.1 : ℝ) * ((1 : ℝ) / (Nat.totient p.2 : ℝ))
        = ∑ p ∈ d.divisors ×ˢ M, (1 : ℝ) / (Nat.totient (p.1 * p.2) : ℝ) := by
          refine Finset.sum_congr rfl fun ⟨a, m⟩ hp => ?_
          simp only [Finset.mem_product, Nat.mem_divisors, M, Finset.mem_filter] at hp
          have hcop_am : Nat.Coprime a m := (hp.2.2.2.coprime_dvd_right hp.1.1).symm
          rw [Nat.totient_mul hcop_am, Nat.cast_mul]; ring
      _ = ∑ k ∈ (d.divisors ×ˢ M).image (fun p => p.1 * p.2), (1 : ℝ) / (Nat.totient k : ℝ) := by
          symm; exact Finset.sum_image (fun a ha b hb h => hinj ha hb h)
      _ ≤ ∑ k ∈ Dset z, (1 : ℝ) / (Nat.totient k : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
          intro k hk
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
          exact hmem p hp
  · simp

private lemma selberg_y_eq {z g : ℕ} (hz : 1 ≤ z) (hg : g ∈ Dset z) :
    ∑ d ∈ (Dset z).filter (fun d => g ∣ d), selbergLam z d / (d : ℝ) =
      (μ g : ℝ) / (Sval z * (Nat.totient g : ℝ)) := by
  have hg_pos : 0 < g := (Finset.mem_Icc.mp (Finset.mem_filter.mp hg).1).1
  have hg_le : g ≤ z := (Finset.mem_Icc.mp (Finset.mem_filter.mp hg).1).2
  set R := (Dset z).filter (fun r => g * r ≤ z ∧ Nat.Coprime r g)
  -- Reindex d = g * r
  have h1 :
      ∑ d ∈ (Dset z).filter (fun d => g ∣ d), selbergLam z d / (d : ℝ) =
        ∑ r ∈ R, selbergLam z (g * r) / ((g * r : ℕ) : ℝ) := by
    symm
    refine Finset.sum_bij (fun r _ => g * r) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [R, Finset.mem_filter] at hr ⊢
      exact ⟨mul_mem_Dset hg hr.1 hr.2.1 hr.2.2.symm, dvd_mul_right g r⟩
    · intro r₁ _ r₂ _ h; exact Nat.eq_of_mul_eq_mul_left hg_pos h
    · intro d hd
      simp only [Finset.mem_filter] at hd
      obtain ⟨hdD, hgd⟩ := hd
      have hd_sq : Squarefree d := (Finset.mem_filter.mp hdD).2.1
      have hcop : Nat.Coprime g (d / g) :=
        (Nat.squarefree_mul_iff.mp ((Nat.mul_div_cancel' hgd).symm ▸ hd_sq)).1
      refine ⟨d / g, ?_, Nat.mul_div_cancel' hgd⟩
      simp only [R, Finset.mem_filter]
      refine ⟨dvd_mem_Dset hdD (Nat.div_dvd_of_dvd hgd), ?_, hcop.symm⟩
      rw [Nat.mul_div_cancel' hgd]
      exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hdD).1).2
    · intro _ _; rfl
  rw [h1]
  have h2 :
      ∑ r ∈ R, selbergLam z (g * r) / ((g * r : ℕ) : ℝ) =
        ((μ g : ℝ) / (Sval z * (Nat.totient g : ℝ))) *
          ∑ r ∈ R, ∑ m ∈ (Dset z).filter (fun m => g * r * m ≤ z ∧ Nat.Coprime m (g * r)),
            (μ r : ℝ) / ((Nat.totient r : ℝ) * (Nat.totient m : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    simp only [R, Finset.mem_filter] at hr
    obtain ⟨hrD, hgr_le, hcop_rg⟩ := hr
    have hgrD : g * r ∈ Dset z := mul_mem_Dset hg hrD hgr_le hcop_rg.symm
    have hgr_pos : 0 < g * r := Nat.mul_pos hg_pos (Finset.mem_Icc.mp (Finset.mem_filter.mp hrD).1).1
    unfold selbergLam
    rw [if_pos hgrD]
    have hmu_mul : (μ (g * r) : ℝ) = (μ g : ℝ) * (μ r : ℝ) := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_rg.symm, Int.cast_mul]
    have hphi_mul : (Nat.totient (g * r) : ℝ) = (Nat.totient g : ℝ) * (Nat.totient r : ℝ) := by
      rw [Nat.totient_mul hcop_rg.symm, Nat.cast_mul]
    rw [hmu_mul, hphi_mul, Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
    have hgr_ne : ((g * r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hgr_pos.ne'
    have hS_ne : Sval z ≠ 0 := (Sval_pos hz).ne'
    have hpg_ne : (Nat.totient g : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hg_pos).ne'
    have hpr_ne : (Nat.totient r : ℝ) ≠ 0 := by
      have hr_pos : 0 < r := (Finset.mem_Icc.mp (Finset.mem_filter.mp hrD).1).1
      exact_mod_cast (Nat.totient_pos.mpr hr_pos).ne'
    refine Finset.sum_congr rfl fun m _ => ?_
    field_simp
  rw [h2]
  -- Swap sum by setting k = r * m ∈ R
  have hinner :
      ∑ r ∈ R, ∑ m ∈ (Dset z).filter (fun m => g * r * m ≤ z ∧ Nat.Coprime m (g * r)),
        (μ r : ℝ) / ((Nat.totient r : ℝ) * (Nat.totient m : ℝ)) = 1 := by
    have hswap :
        ∑ r ∈ R, ∑ m ∈ (Dset z).filter (fun m => g * r * m ≤ z ∧ Nat.Coprime m (g * r)),
          (μ r : ℝ) / ((Nat.totient r : ℝ) * (Nat.totient m : ℝ)) =
        ∑ k ∈ R, ∑ r ∈ k.divisors, (μ r : ℝ) / (Nat.totient k : ℝ) := by
      rw [Finset.sum_sigma', Finset.sum_sigma']
      refine Finset.sum_bij (fun p _ => ⟨p.1 * p.2, p.1⟩) ?_ ?_ ?_ ?_
      · intro ⟨r, m⟩ hp
        simp only [Finset.mem_sigma, R, Finset.mem_filter, Nat.mem_divisors] at hp ⊢
        obtain ⟨⟨hrD, _, hcop_rg⟩, ⟨hmD, hgrm, hcop_mgr⟩⟩ := hp
        have hcop_mg : Nat.Coprime m g := hcop_mgr.coprime_dvd_right (dvd_mul_right g r)
        have hcop_mr : Nat.Coprime m r := hcop_mgr.coprime_dvd_right (dvd_mul_left r g)
        have hrm_le : r * m ≤ z := by
          have : 1 * (r * m) ≤ g * (r * m) := Nat.mul_le_mul_right (r * m) hg_pos
          linarith
        have hrmD : r * m ∈ Dset z := mul_mem_Dset hrD hmD hrm_le hcop_mr.symm
        have hrm_pos : 0 < r * m :=
          Nat.mul_pos (Finset.mem_Icc.mp (Finset.mem_filter.mp hrD).1).1
            (Finset.mem_Icc.mp (Finset.mem_filter.mp hmD).1).1
        refine ⟨⟨hrmD, by linarith, hcop_rg.mul_left hcop_mg⟩, dvd_mul_right r m, hrm_pos.ne'⟩
      · intro ⟨r₁, m₁⟩ hp₁ ⟨r₂, m₂⟩ hp₂ heq
        simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
        obtain ⟨hrm, rfl⟩ := heq
        simp only [Finset.mem_sigma, R, Finset.mem_filter] at hp₁
        have hr_pos : 0 < r₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp₁.1.1).1).1
        have hm : m₁ = m₂ := Nat.eq_of_mul_eq_mul_left hr_pos hrm
        subst hm; rfl
      · intro ⟨k, r⟩ hp
        simp only [Finset.mem_sigma, R, Finset.mem_filter, Nat.mem_divisors] at hp
        obtain ⟨⟨hkD, hgk, hcop_kg⟩, ⟨hrk, hk0⟩⟩ := hp
        have hk_sq : Squarefree k := (Finset.mem_filter.mp hkD).2.1
        have hrD : r ∈ Dset z := dvd_mem_Dset hkD hrk
        have hmD : k / r ∈ Dset z := dvd_mem_Dset hkD (Nat.div_dvd_of_dvd hrk)
        have hcop_rm : Nat.Coprime r (k / r) :=
          (Nat.squarefree_mul_iff.mp ((Nat.mul_div_cancel' hrk).symm ▸ hk_sq)).1
        have hcop_rg : Nat.Coprime r g := hcop_kg.coprime_dvd_left hrk
        have hcop_mg : Nat.Coprime (k / r) g := hcop_kg.coprime_dvd_left (Nat.div_dvd_of_dvd hrk)
        have hgr_le : g * r ≤ z :=
          le_trans (Nat.mul_le_mul_left g (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hrk)) hgk
        refine ⟨⟨r, k / r⟩, ?_, ?_⟩
        · simp only [Finset.mem_sigma, R, Finset.mem_filter]
          refine ⟨⟨hrD, hgr_le, hcop_rg⟩, hmD, ?_, hcop_mg.mul_right hcop_rm.symm⟩
          rw [mul_assoc, Nat.mul_div_cancel' hrk]; exact hgk
        · simp [Nat.mul_div_cancel' hrk]
      · intro ⟨r, m⟩ hp
        simp only [Finset.mem_sigma, R, Finset.mem_filter] at hp
        have hcop_mr : Nat.Coprime m r := hp.2.2.2.coprime_dvd_right (dvd_mul_left r g)
        rw [Nat.totient_mul hcop_mr.symm, Nat.cast_mul]
    rw [hswap]
    have h1mem : 1 ∈ R := by
      simp only [R, Finset.mem_filter]
      exact ⟨one_mem_Dset hz, by linarith, Nat.coprime_one_left g⟩
    rw [Finset.sum_eq_single 1]
    · simp
    · intro k _ hk1
      rw [← Finset.sum_div, ← Int.cast_sum]
      have hmz : ∑ r ∈ k.divisors, μ r = 0 := by
        have h := congrArg (fun f => f k) ArithmeticFunction.moebius_mul_coe_zeta
        rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply, if_neg hk1] at h
        exact h
      rw [hmz, Int.cast_zero, zero_div]
    · intro h; exact (h h1mem).elim
  rw [hinner, mul_one]

private lemma card_Icc_dvd (Y L : ℕ) (hL : 1 ≤ L) :
    #((Finset.Icc 1 Y).filter (fun m => L ∣ m)) = Y / L := by
  have heq : (Finset.Icc 1 Y).filter (fun m => L ∣ m) = (Finset.Icc 1 (Y / L)).image (fun k => L * k) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hm1, hmY⟩, ⟨k, rfl⟩⟩
      have hk1 : 1 ≤ k := by
        by_contra h0
        have hk0 : k = 0 := by omega
        rw [hk0, mul_zero] at hm1
        omega
      have hkY : k ≤ Y / L := (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
      exact ⟨k, ⟨hk1, hkY⟩, rfl⟩
    · rintro ⟨k, ⟨hk1, hkY⟩, rfl⟩
      exact ⟨⟨Nat.mul_pos hL hk1, le_trans (Nat.mul_le_mul_left L hkY) (Nat.mul_div_le Y L)⟩,
        dvd_mul_right L k⟩
  rw [heq, Finset.card_image_of_injective _ (mul_right_injective₀ (by omega : L ≠ 0))]
  simp

private lemma selberg_sieve_isNotP3 {Y z : ℕ} (_hY : 1 ≤ Y) (hz : 1 ≤ z) :
    (#((Finset.Icc 1 Y).filter isNotP3) : ℝ) ≤ (Y : ℝ) / Sval z + (z : ℝ) ^ 2 := by
  -- Step 1: Indicator bound
  have h1 : (#((Finset.Icc 1 Y).filter isNotP3) : ℝ) ≤
      ∑ m ∈ Finset.Icc 1 Y, (∑ d ∈ (Dset z).filter (fun d => d ∣ m), selbergLam z d) ^ 2 := by
    calc (#((Finset.Icc 1 Y).filter isNotP3) : ℝ)
        = ∑ m ∈ (Finset.Icc 1 Y).filter isNotP3,
            (∑ d ∈ (Dset z).filter (fun d => d ∣ m), selbergLam z d) ^ 2 := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
          refine Finset.sum_congr rfl fun m hm => ?_
          simp only [Finset.mem_filter, Finset.mem_Icc] at hm
          obtain ⟨⟨hm1, _⟩, hmNotP3⟩ := hm
          have hfilt : (Dset z).filter (fun d => d ∣ m) = {1} := by
            ext d
            simp only [Finset.mem_filter, Finset.mem_singleton]
            constructor
            · rintro ⟨hdD, hdm⟩
              have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hdD).1).1
              have hdP3 : isP3 d := (Finset.mem_filter.mp hdD).2.2
              by_contra hdne1
              obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd hdne1
              have hpm : p ∈ m.primeFactors :=
                Nat.mem_primeFactors.mpr ⟨hp.1, dvd_trans hp.2 hdm, by omega⟩
              have hpd : p ∈ d.primeFactors :=
                Nat.mem_primeFactors.mpr ⟨hp.1, hp.2, by omega⟩
              exact hmNotP3 p hpm (hdP3 p hpd)
            · rintro rfl
              exact ⟨one_mem_Dset hz, one_dvd m⟩
          rw [hfilt, Finset.sum_singleton, selbergLam_one hz, one_pow]
      _ ≤ ∑ m ∈ Finset.Icc 1 Y, (∑ d ∈ (Dset z).filter (fun d => d ∣ m), selbergLam z d) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
  -- Step 2: Expand square and swap sums
  have h2 :
      ∑ m ∈ Finset.Icc 1 Y, (∑ d ∈ (Dset z).filter (fun d => d ∣ m), selbergLam z d) ^ 2 =
        ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z,
          selbergLam z d₁ * selbergLam z d₂ * ((Y / Nat.lcm d₁ d₂ : ℕ) : ℝ) := by
    have hexp : ∀ m ∈ Finset.Icc 1 Y,
        (∑ d ∈ (Dset z).filter (fun d => d ∣ m), selbergLam z d) ^ 2 =
          ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z,
            if Nat.lcm d₁ d₂ ∣ m then selbergLam z d₁ * selbergLam z d₂ else 0 := by
      intro m _
      rw [sq, Finset.sum_mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun d₁ _ => ?_
      rw [Finset.sum_filter]
      by_cases h1m : d₁ ∣ m
      · rw [if_pos h1m]
        refine Finset.sum_congr rfl fun d₂ _ => ?_
        by_cases h2m : d₂ ∣ m
        · rw [if_pos h2m, if_pos (Nat.lcm_dvd h1m h2m)]
        · rw [if_neg h2m, if_neg (fun h => h2m (dvd_trans (Nat.dvd_lcm_right d₁ d₂) h))]
      · rw [if_neg h1m]
        symm
        refine Finset.sum_eq_zero fun d₂ _ => ?_
        rw [if_neg (fun h => h1m (dvd_trans (Nat.dvd_lcm_left d₁ d₂) h))]
    rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₂ hd₂ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hd₁_pos : 0 < d₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd₁).1).1
    have hd₂_pos : 0 < d₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd₂).1).1
    have hlcm_pos : 1 ≤ Nat.lcm d₁ d₂ := Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd₁_pos.ne' hd₂_pos.ne')
    rw [card_Icc_dvd Y (Nat.lcm d₁ d₂) hlcm_pos]
  -- Step 3: Split Y / lcm into main term (Y / lcm in ℝ) and remainder
  have hmain :
      ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z,
        selbergLam z d₁ * selbergLam z d₂ / (Nat.lcm d₁ d₂ : ℝ) = 1 / Sval z := by
    have hstep :
        ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z,
          selbergLam z d₁ * selbergLam z d₂ / (Nat.lcm d₁ d₂ : ℝ) =
        ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z, ∑ g ∈ Dset z,
          if g ∣ d₁ ∧ g ∣ d₂ then
            (Nat.totient g : ℝ) * (selbergLam z d₁ / (d₁ : ℝ)) * (selbergLam z d₂ / (d₂ : ℝ))
          else 0 := by
      refine Finset.sum_congr rfl fun d₁ hd₁ => Finset.sum_congr rfl fun d₂ hd₂ => ?_
      have hd₁_pos : 0 < d₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd₁).1).1
      have hd₂_pos : 0 < d₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd₂).1).1
      have hlcm_eq : (Nat.gcd d₁ d₂ : ℝ) * (Nat.lcm d₁ d₂ : ℝ) = (d₁ : ℝ) * (d₂ : ℝ) := by
        exact_mod_cast Nat.gcd_mul_lcm d₁ d₂
      have hlcm_pos : (0 : ℝ) < Nat.lcm d₁ d₂ := by
        exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd₁_pos.ne' hd₂_pos.ne')
      have hdiv : (1 : ℝ) / (Nat.lcm d₁ d₂ : ℝ) = (Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) := by
        rw [div_eq_div_iff hlcm_pos.ne' (by positivity), one_mul, hlcm_eq]
      rw [← Finset.sum_filter]
      have hfilt_eq : (Dset z).filter (fun g => g ∣ d₁ ∧ g ∣ d₂) = (Nat.gcd d₁ d₂).divisors := by
        ext g
        simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
        constructor
        · rintro ⟨_, h12⟩
          exact ⟨h12, (Nat.gcd_pos_of_pos_left d₂ hd₁_pos).ne'⟩
        · rintro ⟨h12, _⟩
          exact ⟨dvd_mem_Dset hd₁ h12.1, h12⟩
      rw [hfilt_eq]
      calc selbergLam z d₁ * selbergLam z d₂ / (Nat.lcm d₁ d₂ : ℝ)
          = (selbergLam z d₁ * selbergLam z d₂) * ((Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ))) := by
            rw [← hdiv, mul_one_div]
        _ = ((Nat.gcd d₁ d₂ : ℝ)) * ((selbergLam z d₁ / (d₁ : ℝ)) * (selbergLam z d₂ / (d₂ : ℝ))) := by
            ring
        _ = (∑ g ∈ (Nat.gcd d₁ d₂).divisors, (Nat.totient g : ℝ)) *
              ((selbergLam z d₁ / (d₁ : ℝ)) * (selbergLam z d₂ / (d₂ : ℝ))) := by
            rw [← Nat.cast_sum, Nat.sum_totient]
        _ = ∑ g ∈ (Nat.gcd d₁ d₂).divisors,
              (Nat.totient g : ℝ) * (selbergLam z d₁ / (d₁ : ℝ)) * (selbergLam z d₂ / (d₂ : ℝ)) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun g _ => by ring
    rw [hstep]
    -- Swap g to the outside
    have hswap :
        ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z, ∑ g ∈ Dset z,
          (if g ∣ d₁ ∧ g ∣ d₂ then
            (Nat.totient g : ℝ) * (selbergLam z d₁ / (d₁ : ℝ)) * (selbergLam z d₂ / (d₂ : ℝ))
          else 0) =
        ∑ g ∈ Dset z, (Nat.totient g : ℝ) *
          (∑ d ∈ (Dset z).filter (fun d => g ∣ d), selbergLam z d / (d : ℝ)) ^ 2 := by
      have hs1 :
          ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z, ∑ g ∈ Dset z,
            (if g ∣ d₁ ∧ g ∣ d₂ then
              (Nat.totient g : ℝ) * (selbergLam z d₁ / (d₁ : ℝ)) * (selbergLam z d₂ / (d₂ : ℝ))
            else 0) =
          ∑ g ∈ Dset z, ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z,
            (if g ∣ d₁ ∧ g ∣ d₂ then
              (Nat.totient g : ℝ) * (selbergLam z d₁ / (d₁ : ℝ)) * (selbergLam z d₂ / (d₂ : ℝ))
            else 0) := by
        conv_lhs =>
          arg 2; ext d₁
          rw [Finset.sum_comm]
        rw [Finset.sum_comm]
      rw [hs1]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun d₁ _ => ?_
      by_cases h1g : g ∣ d₁
      · rw [if_pos h1g, Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun d₂ _ => ?_
        by_cases h2g : g ∣ d₂
        · rw [if_pos ⟨h1g, h2g⟩, if_pos h2g]; ring
        · simp [h2g]
      · rw [if_neg h1g]
        simp [h1g]
    rw [hswap]
    have hS_ne : Sval z ≠ 0 := (Sval_pos hz).ne'
    calc ∑ g ∈ Dset z, (Nat.totient g : ℝ) *
            (∑ d ∈ (Dset z).filter (fun d => g ∣ d), selbergLam z d / (d : ℝ)) ^ 2
        = ∑ g ∈ Dset z, (Nat.totient g : ℝ) * ((μ g : ℝ) / (Sval z * (Nat.totient g : ℝ))) ^ 2 := by
          refine Finset.sum_congr rfl fun g hg => by rw [selberg_y_eq hz hg]
      _ = (1 / (Sval z) ^ 2) * ∑ g ∈ Dset z, (1 : ℝ) / (Nat.totient g : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g hg => ?_
          have hg_sq : Squarefree g := (Finset.mem_filter.mp hg).2.1
          have hg_pos : 0 < g := (Finset.mem_Icc.mp (Finset.mem_filter.mp hg).1).1
          have hpg_ne : (Nat.totient g : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hg_pos).ne'
          have hmu2 : (μ g : ℝ) ^ 2 = 1 := by
            exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hg_sq
          rw [div_pow, hmu2]
          field_simp
      _ = (1 / (Sval z) ^ 2) * Sval z := rfl
      _ = 1 / Sval z := by field_simp
  -- Step 4: Bound error term by z^2
  have herr :
      ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z,
        selbergLam z d₁ * selbergLam z d₂ *
          (((Y / Nat.lcm d₁ d₂ : ℕ) : ℝ) - (Y : ℝ) / (Nat.lcm d₁ d₂ : ℝ)) ≤ (z : ℝ) ^ 2 := by
    calc ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z,
            selbergLam z d₁ * selbergLam z d₂ *
              (((Y / Nat.lcm d₁ d₂ : ℕ) : ℝ) - (Y : ℝ) / (Nat.lcm d₁ d₂ : ℝ))
        ≤ ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z, (1 : ℝ) := by
          refine Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => ?_
          have hd₁_pos : 0 < d₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd₁).1).1
          have hd₂_pos : 0 < d₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd₂).1).1
          set L := Nat.lcm d₁ d₂
          have hL_pos : 0 < L := Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd₁_pos.ne' hd₂_pos.ne')
          have hrem_abs : |((Y / L : ℕ) : ℝ) - (Y : ℝ) / (L : ℝ)| ≤ 1 := by
            have hle1 : ((Y / L : ℕ) : ℝ) ≤ (Y : ℝ) / (L : ℝ) := by
              rw [le_div_iff₀ (by exact_mod_cast hL_pos)]
              exact_mod_cast Nat.div_mul_le_self Y L
            have hlt2 : (Y : ℝ) / (L : ℝ) ≤ ((Y / L : ℕ) : ℝ) + 1 := by
              rw [div_le_iff₀ (by exact_mod_cast hL_pos)]
              have hlt : Y < (Y / L + 1) * L := by
                have := Nat.div_add_mod Y L
                have := Nat.mod_lt Y hL_pos
                nlinarith
              exact_mod_cast hlt.le
            rw [abs_le]
            exact ⟨by linarith, by linarith⟩
          have hl1 := abs_selbergLam_le_one hz d₁
          have hl2 := abs_selbergLam_le_one hz d₂
          have hprod_abs : |selbergLam z d₁ * selbergLam z d₂ *
              (((Y / L : ℕ) : ℝ) - (Y : ℝ) / (L : ℝ))| ≤ 1 := by
            rw [abs_mul, abs_mul]
            calc |selbergLam z d₁| * |selbergLam z d₂| * |((Y / L : ℕ) : ℝ) - (Y : ℝ) / (L : ℝ)|
                ≤ 1 * 1 * 1 := by
                  exact mul_le_mul (mul_le_mul hl1 hl2 (abs_nonneg _) zero_le_one)
                    hrem_abs (abs_nonneg _) (by norm_num)
              _ = 1 := by norm_num
          exact (le_abs_self _).trans hprod_abs
      _ = (#(Dset z) : ℝ) ^ 2 := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one, sq]
      _ ≤ (z : ℝ) ^ 2 := by
          have hc : #(Dset z) ≤ z := by
            calc #(Dset z) ≤ #(Finset.Icc 1 z) := Finset.card_filter_le _ _
              _ = z := by simp
          exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hc) 2
  have hcombine :
      ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z,
        selbergLam z d₁ * selbergLam z d₂ * ((Y / Nat.lcm d₁ d₂ : ℕ) : ℝ) =
      (Y : ℝ) * (∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z,
          selbergLam z d₁ * selbergLam z d₂ / (Nat.lcm d₁ d₂ : ℝ)) +
        ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z,
          selbergLam z d₁ * selbergLam z d₂ *
            (((Y / Nat.lcm d₁ d₂ : ℕ) : ℝ) - (Y : ℝ) / (Nat.lcm d₁ d₂ : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d₂ _ => by ring
  rw [h2, hcombine, hmain] at h1
  linarith [show (Y : ℝ) * (1 / Sval z) = (Y : ℝ) / Sval z by ring]

private noncomputable def C_notP3 : ℝ := 6 * Real.exp 14 + 10

private lemma C_notP3_pos : 0 < C_notP3 := by
  unfold C_notP3; positivity

private lemma card_isNotP3_le {Y : ℕ} (hY : 2 ≤ Y) :
    (#((Finset.Icc 1 Y).filter isNotP3) : ℝ) ≤
      C_notP3 * (Y : ℝ) / Real.sqrt (Real.log (Y : ℝ)) := by
  have hlogY_pos : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Y))
  have hrtY_pos : 0 < Real.sqrt (Real.log (Y : ℝ)) := Real.sqrt_pos.mpr hlogY_pos
  by_cases hY81 : Y < 81
  · have hc : (#((Finset.Icc 1 Y).filter isNotP3) : ℝ) ≤ (Y : ℝ) := by
      have : #((Finset.Icc 1 Y).filter isNotP3) ≤ Y :=
        (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    have hrt_le : Real.sqrt (Real.log (Y : ℝ)) ≤ 9 := by
      have h1 : Real.log (Y : ℝ) ≤ 81 := by
        have hY_le : (Y : ℝ) ≤ 81 := by exact_mod_cast hY81.le
        linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < Y)]
      calc Real.sqrt (Real.log (Y : ℝ)) ≤ Real.sqrt 81 := Real.sqrt_le_sqrt h1
        _ = 9 := by rw [show (81 : ℝ) = 9 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [le_div_iff₀ hrtY_pos]
    have hC9 : 9 ≤ C_notP3 := by unfold C_notP3; linarith [Real.exp_pos 14]
    calc (#((Finset.Icc 1 Y).filter isNotP3) : ℝ) * Real.sqrt (Real.log (Y : ℝ))
        ≤ (Y : ℝ) * 9 := mul_le_mul hc hrt_le hrtY_pos.le (by positivity)
      _ ≤ C_notP3 * (Y : ℝ) := by nlinarith
  · have hY81' : 81 ≤ Y := by omega
    set z := Nat.sqrt (Nat.sqrt Y)
    have hsqY : 9 ≤ Nat.sqrt Y := Nat.le_sqrt.mpr (by omega)
    have hz3 : 3 ≤ z := Nat.le_sqrt.mpr (by omega)
    have hz1 : 1 ≤ z := by omega
    have hsieve := selberg_sieve_isNotP3 (by omega : 1 ≤ Y) hz1
    have hSval := Sval_lower_bound hz3
    -- Compare log z and log Y: Y < (z+1)^4 ≤ z^8
    have hY_lt : Y < z ^ 8 := by
      have h1 : Nat.sqrt Y < (z + 1) ^ 2 := by
        have := Nat.lt_succ_sqrt (Nat.sqrt Y); nlinarith
      have h2 : Y < (Nat.sqrt Y + 1) ^ 2 := by
        have := Nat.lt_succ_sqrt Y; nlinarith
      have h3 : Nat.sqrt Y + 1 ≤ (z + 1) ^ 2 := by omega
      have h4 : Y < (z + 1) ^ 4 := by
        calc Y < (Nat.sqrt Y + 1) ^ 2 := h2
          _ ≤ ((z + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h3 2
          _ = (z + 1) ^ 4 := by ring
      have h5 : z + 1 ≤ z ^ 2 := by nlinarith
      calc Y < (z + 1) ^ 4 := h4
        _ ≤ (z ^ 2) ^ 4 := Nat.pow_le_pow_left h5 4
        _ = z ^ 8 := by ring
    have hlog_cmp : Real.log (Y : ℝ) ≤ 8 * Real.log (z : ℝ) := by
      calc Real.log (Y : ℝ) ≤ Real.log ((z ^ 8 : ℕ) : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hY_lt.le)
        _ = 8 * Real.log (z : ℝ) := by rw [Nat.cast_pow, Real.log_pow]; norm_num
    have hrt_cmp : Real.sqrt (Real.log (Y : ℝ)) ≤ 3 * Real.sqrt (Real.log (z : ℝ)) := by
      have h1 : Real.sqrt (Real.log (Y : ℝ)) ≤ Real.sqrt (9 * Real.log (z : ℝ)) :=
        Real.sqrt_le_sqrt (by
          have hlogz : 0 ≤ Real.log (z : ℝ) := Real.log_nonneg (by exact_mod_cast hz1)
          linarith)
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 9 = 3 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h1
      exact h1
    have hSvalY : Real.sqrt (Real.log (Y : ℝ)) / (6 * Real.exp 14) ≤ Sval z := by
      calc Real.sqrt (Real.log (Y : ℝ)) / (6 * Real.exp 14)
          ≤ (3 * Real.sqrt (Real.log (z : ℝ))) / (6 * Real.exp 14) :=
            div_le_div_of_nonneg_right hrt_cmp (by positivity)
        _ = Real.sqrt (Real.log (z : ℝ)) / (2 * Real.exp 14) := by ring
        _ ≤ Sval z := hSval
    have hterm1 : (Y : ℝ) / Sval z ≤
        (6 * Real.exp 14) * (Y : ℝ) / Real.sqrt (Real.log (Y : ℝ)) := by
      have hSpos : 0 < Sval z := Sval_pos hz1
      rw [div_le_div_iff₀ hSpos hrtY_pos]
      have hmul := mul_le_mul_of_nonneg_left hSvalY (show (0 : ℝ) ≤ 6 * Real.exp 14 by positivity)
      have hsimp : (6 * Real.exp 14) * (Real.sqrt (Real.log (Y : ℝ)) / (6 * Real.exp 14)) =
          Real.sqrt (Real.log (Y : ℝ)) := by field_simp
      rw [hsimp] at hmul
      nlinarith
    have hterm2 : (z : ℝ) ^ 2 ≤ (Y : ℝ) / Real.sqrt (Real.log (Y : ℝ)) := by
      have hz2_le : (z : ℝ) ^ 2 ≤ Real.sqrt (Y : ℝ) := by
        rw [Real.le_sqrt (by positivity) (by positivity)]
        have hnat : z ^ 4 ≤ Y := by
          have h1 : z * z ≤ Nat.sqrt Y := Nat.sqrt_le (Nat.sqrt Y)
          have h2 : Nat.sqrt Y * Nat.sqrt Y ≤ Y := Nat.sqrt_le Y
          nlinarith
        have : ((z : ℝ) ^ 2) ^ 2 = ((z ^ 4 : ℕ) : ℝ) := by push_cast; ring
        rw [this]
        exact_mod_cast hnat
      have hrtlog_le : Real.sqrt (Real.log (Y : ℝ)) ≤ Real.sqrt (Y : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < Y)]
      rw [le_div_iff₀ hrtY_pos]
      calc (z : ℝ) ^ 2 * Real.sqrt (Real.log (Y : ℝ))
          ≤ Real.sqrt (Y : ℝ) * Real.sqrt (Y : ℝ) :=
            mul_le_mul hz2_le hrtlog_le hrtY_pos.le (Real.sqrt_nonneg _)
        _ = (Y : ℝ) := Real.mul_self_sqrt (by positivity)
    calc (#((Finset.Icc 1 Y).filter isNotP3) : ℝ)
        ≤ (Y : ℝ) / Sval z + (z : ℝ) ^ 2 := hsieve
      _ ≤ (6 * Real.exp 14) * (Y : ℝ) / Real.sqrt (Real.log (Y : ℝ)) +
            (Y : ℝ) / Real.sqrt (Real.log (Y : ℝ)) := add_le_add hterm1 hterm2
      _ = (6 * Real.exp 14 + 1) * (Y : ℝ) / Real.sqrt (Real.log (Y : ℝ)) := by ring
      _ ≤ C_notP3 * (Y : ℝ) / Real.sqrt (Real.log (Y : ℝ)) := by
          apply div_le_div_of_nonneg_right _ hrtY_pos.le
          unfold C_notP3
          nlinarith

/- ### Section 4: Upper bound on sums of two squares up to `X` -/

private noncomputable def sumTwoSqSet (X : ℕ) : Finset ℕ :=
  (Finset.Icc 0 X).filter (fun k => ∃ a b : ℕ, k = a ^ 2 + b ^ 2)

private lemma sum_inv_sq_Icc_le (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ s ∈ Finset.Icc a b, (1 : ℝ) / ((s : ℝ) ^ 2) ≤ 1 / ((a - 1 : ℕ) : ℝ) := by
  calc ∑ s ∈ Finset.Icc a b, (1 : ℝ) / ((s : ℝ) ^ 2)
      ≤ ∑ s ∈ Finset.Icc a b, (1 : ℝ) / ((s : ℝ) * ((s : ℝ) - 1)) := by
        refine Finset.sum_le_sum fun s hs => ?_
        have hs2 : 2 ≤ s := le_trans ha (Finset.mem_Icc.mp hs).1
        have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs2
        apply one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
    _ = ∑ s ∈ Finset.Ico a (b + 1), (1 / ((s - 1 : ℕ) : ℝ) - 1 / (s : ℝ)) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        have hs2 : 2 ≤ s := le_trans ha (Finset.mem_Icc.mp hs).1
        have hs1 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
        have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs2
        rw [hs1]
        have h1 : (s : ℝ) ≠ 0 := by linarith
        have h2 : (s : ℝ) - 1 ≠ 0 := by linarith
        field_simp; ring
    _ = 1 / ((a - 1 : ℕ) : ℝ) - 1 / (b : ℝ) := by
        have htele : ∀ n, a ≤ n →
            ∑ s ∈ Finset.Ico a n, (1 / ((s - 1 : ℕ) : ℝ) - 1 / (s : ℝ)) =
              1 / ((a - 1 : ℕ) : ℝ) - 1 / ((n - 1 : ℕ) : ℝ) := by
          intro n hn
          induction n with
          | zero => omega
          | succ n ih =>
            by_cases hna : n + 1 = a
            · rw [hna, Finset.Ico_self, Finset.sum_empty, sub_self]
            · rw [Finset.sum_Ico_succ_top (by omega : a ≤ n), ih (by omega), Nat.add_sub_cancel]
              ring
        rw [htele (b + 1) (by omega), Nat.add_sub_cancel]
    _ ≤ 1 / ((a - 1 : ℕ) : ℝ) := by
        have : 0 ≤ 1 / (b : ℝ) := by positivity
        linarith

private noncomputable def C_twoSq : ℝ := 4 * C_notP3 + 3

private lemma C_twoSq_pos : 0 < C_twoSq := by
  unfold C_twoSq; linarith [C_notP3_pos]

private lemma card_sumTwoSqSet_le {X : ℕ} (hX : 16 ≤ X) :
    (#(sumTwoSqSet X) : ℝ) ≤ C_twoSq * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) := by
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hrtX_pos : 0 < Real.sqrt (Real.log (X : ℝ)) := Real.sqrt_pos.mpr hlogX_pos
  -- Cover positive elements of sumTwoSqSet X by ⋃_{s=1}^{√X} {s^2 * m | m ≤ X/s^2, isNotP3 m}
  have hcover :
      (sumTwoSqSet X).erase 0 ⊆
        (Finset.Icc 1 (Nat.sqrt X)).biUnion fun s =>
          ((Finset.Icc 1 (X / s ^ 2)).filter isNotP3).image (fun m => s ^ 2 * m) := by
    intro k hk
    simp only [sumTwoSqSet, Finset.mem_erase, Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨hk0, ⟨_, hkX⟩, hsq⟩ := hk
    obtain ⟨s, m, hkm, hissq⟩ := Nat.eq_sq_add_sq_iff_eq_sq_mul.mp hsq
    have hs_pos : 1 ≤ s := by
      by_contra h0
      have hs0 : s = 0 := by omega
      rw [hs0] at hkm
      simp at hkm
      exact hk0 hkm
    have hm_pos : 1 ≤ m := by
      by_contra h0
      have hm0 : m = 0 := by omega
      rw [hm0] at hkm
      simp at hkm
      exact hk0 hkm
    have hs_le : s ≤ Nat.sqrt X := by
      apply Nat.le_sqrt.mpr
      have : s * s ≤ s ^ 2 * m := by nlinarith
      omega
    have hm_le : m ≤ X / s ^ 2 := by
      rw [Nat.le_div_iff_mul_le (pow_pos (by omega) 2)]
      nlinarith
    have hm_notP3 : isNotP3 m := fun p hp =>
      Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one hp hissq
    rw [Finset.mem_biUnion]
    refine ⟨s, Finset.mem_Icc.mpr ⟨hs_pos, hs_le⟩, Finset.mem_image.mpr ?_⟩
    exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm_pos, hm_le⟩, hm_notP3⟩, hkm.symm⟩
  have hcard_pos :
      (#((sumTwoSqSet X).erase 0) : ℝ) ≤
        ∑ s ∈ Finset.Icc 1 (Nat.sqrt X),
          (#((Finset.Icc 1 (X / s ^ 2)).filter isNotP3) : ℝ) := by
    have hnat : #((sumTwoSqSet X).erase 0) ≤
        ∑ s ∈ Finset.Icc 1 (Nat.sqrt X), #((Finset.Icc 1 (X / s ^ 2)).filter isNotP3) := by
      calc #((sumTwoSqSet X).erase 0)
          ≤ #((Finset.Icc 1 (Nat.sqrt X)).biUnion fun s =>
                ((Finset.Icc 1 (X / s ^ 2)).filter isNotP3).image (fun m => s ^ 2 * m)) :=
            Finset.card_le_card hcover
        _ ≤ ∑ s ∈ Finset.Icc 1 (Nat.sqrt X),
              #(((Finset.Icc 1 (X / s ^ 2)).filter isNotP3).image (fun m => s ^ 2 * m)) :=
            Finset.card_biUnion_le
        _ ≤ ∑ s ∈ Finset.Icc 1 (Nat.sqrt X), #((Finset.Icc 1 (X / s ^ 2)).filter isNotP3) :=
            Finset.sum_le_sum fun _ _ => Finset.card_image_le
    exact_mod_cast hnat
  -- Split s at S₀ = √(√X)
  set S₀ := Nat.sqrt (Nat.sqrt X)
  have hsqX : 4 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  have hS0_ge2 : 2 ≤ S₀ := Nat.le_sqrt.mpr (by omega)
  have hS0_le : S₀ ≤ Nat.sqrt X := Nat.sqrt_le_self (Nat.sqrt X)
  have hsplit :
      ∑ s ∈ Finset.Icc 1 (Nat.sqrt X), (#((Finset.Icc 1 (X / s ^ 2)).filter isNotP3) : ℝ) =
        ∑ s ∈ Finset.Icc 1 S₀, (#((Finset.Icc 1 (X / s ^ 2)).filter isNotP3) : ℝ) +
        ∑ s ∈ Finset.Icc (S₀ + 1) (Nat.sqrt X), (#((Finset.Icc 1 (X / s ^ 2)).filter isNotP3) : ℝ) := by
    have hU : Finset.Icc 1 (Nat.sqrt X) = Finset.Icc 1 S₀ ∪ Finset.Icc (S₀ + 1) (Nat.sqrt X) := by
      ext s; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    rw [hU, Finset.sum_union]
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    simp only [Finset.mem_Icc] at hs1 hs2; omega
  -- Small s ≤ S₀
  have hsmall :
      ∑ s ∈ Finset.Icc 1 S₀, (#((Finset.Icc 1 (X / s ^ 2)).filter isNotP3) : ℝ) ≤
        4 * C_notP3 * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) := by
    have hterm : ∀ s ∈ Finset.Icc 1 S₀,
        (#((Finset.Icc 1 (X / s ^ 2)).filter isNotP3) : ℝ) ≤
          (2 * C_notP3 * (X : ℝ) / Real.sqrt (Real.log (X : ℝ))) * ((1 : ℝ) / ((s : ℝ) ^ 2)) := by
      intro s hs
      simp only [Finset.mem_Icc] at hs
      obtain ⟨hs1, hsS0⟩ := hs
      set Y := X / s ^ 2
      have hs2_le : s ^ 2 ≤ Nat.sqrt X := by
        have h1 : s * s ≤ S₀ * S₀ := Nat.mul_le_mul hsS0 hsS0
        have h2 : S₀ * S₀ ≤ Nat.sqrt X := Nat.sqrt_le (Nat.sqrt X)
        nlinarith
      have hY_ge_sq : Nat.sqrt X ≤ Y := by
        rw [Nat.le_div_iff_mul_le (pow_pos (by omega) 2)]
        have h1 : Nat.sqrt X * s ^ 2 ≤ Nat.sqrt X * Nat.sqrt X := Nat.mul_le_mul_left _ hs2_le
        have h2 : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
        omega
      have hY2 : 2 ≤ Y := by omega
      have hY_cube : X < Y ^ 3 := by
        have h1 : X < (Nat.sqrt X + 1) ^ 2 := by
          have := Nat.lt_succ_sqrt X; nlinarith
        have h2 : (Nat.sqrt X + 1) ^ 2 ≤ (Nat.sqrt X) ^ 3 := by nlinarith
        have h3 : (Nat.sqrt X) ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left hY_ge_sq 3
        omega
      have hlogY_ge : Real.log (X : ℝ) ≤ 3 * Real.log (Y : ℝ) := by
        calc Real.log (X : ℝ) ≤ Real.log ((Y ^ 3 : ℕ) : ℝ) :=
              Real.log_le_log (by positivity) (by exact_mod_cast hY_cube.le)
          _ = 3 * Real.log (Y : ℝ) := by rw [Nat.cast_pow, Real.log_pow]; norm_num
      have hrtY_ge : Real.sqrt (Real.log (X : ℝ)) ≤ 2 * Real.sqrt (Real.log (Y : ℝ)) := by
        have hlogY_nn : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))
        have h1 : Real.sqrt (Real.log (X : ℝ)) ≤ Real.sqrt (4 * Real.log (Y : ℝ)) :=
          Real.sqrt_le_sqrt (by linarith)
        rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h1
        exact h1
      have hY_le : (Y : ℝ) ≤ (X : ℝ) / ((s : ℝ) ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        exact_mod_cast Nat.div_mul_le_self X (s ^ 2)
      have hrtY_pos : 0 < Real.sqrt (Real.log (Y : ℝ)) :=
        Real.sqrt_pos.mpr (Real.log_pos (by exact_mod_cast (by omega : 1 < Y)))
      calc (#((Finset.Icc 1 Y).filter isNotP3) : ℝ)
          ≤ C_notP3 * (Y : ℝ) / Real.sqrt (Real.log (Y : ℝ)) := card_isNotP3_le hY2
        _ ≤ C_notP3 * ((X : ℝ) / ((s : ℝ) ^ 2)) / (Real.sqrt (Real.log (X : ℝ)) / 2) := by
            have hCpos := C_notP3_pos
            apply div_le_div₀ (by positivity)
              (mul_le_mul_of_nonneg_left hY_le hCpos.le)
              (by positivity) (by linarith)
        _ = (2 * C_notP3 * (X : ℝ) / Real.sqrt (Real.log (X : ℝ))) * ((1 : ℝ) / ((s : ℝ) ^ 2)) := by
            ring
    calc ∑ s ∈ Finset.Icc 1 S₀, (#((Finset.Icc 1 (X / s ^ 2)).filter isNotP3) : ℝ)
        ≤ ∑ s ∈ Finset.Icc 1 S₀,
            (2 * C_notP3 * (X : ℝ) / Real.sqrt (Real.log (X : ℝ))) * ((1 : ℝ) / ((s : ℝ) ^ 2)) :=
          Finset.sum_le_sum hterm
      _ = (2 * C_notP3 * (X : ℝ) / Real.sqrt (Real.log (X : ℝ))) *
            ∑ s ∈ Finset.Icc 1 S₀, (1 : ℝ) / ((s : ℝ) ^ 2) := (Finset.mul_sum _ _ _).symm
      _ ≤ (2 * C_notP3 * (X : ℝ) / Real.sqrt (Real.log (X : ℝ))) * 2 := by
          have hCpos := C_notP3_pos
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hI : Finset.Icc 1 S₀ = insert 1 (Finset.Icc 2 S₀) := by
            ext s; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hI, Finset.sum_insert (by simp)]
          have htail := sum_inv_sq_Icc_le 2 S₀ le_rfl hS0_ge2
          norm_num at htail ⊢
          linarith
      _ = 4 * C_notP3 * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) := by ring
  -- Large s > S₀
  have hlarge :
      ∑ s ∈ Finset.Icc (S₀ + 1) (Nat.sqrt X), (#((Finset.Icc 1 (X / s ^ 2)).filter isNotP3) : ℝ) ≤
        2 * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) := by
    by_cases hempty : Nat.sqrt X < S₀ + 1
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; positivity
    have hle : S₀ + 1 ≤ Nat.sqrt X := by omega
    have h1 :
        ∑ s ∈ Finset.Icc (S₀ + 1) (Nat.sqrt X), (#((Finset.Icc 1 (X / s ^ 2)).filter isNotP3) : ℝ) ≤
          (X : ℝ) / (S₀ : ℝ) := by
      calc ∑ s ∈ Finset.Icc (S₀ + 1) (Nat.sqrt X),
              (#((Finset.Icc 1 (X / s ^ 2)).filter isNotP3) : ℝ)
          ≤ ∑ s ∈ Finset.Icc (S₀ + 1) (Nat.sqrt X), (X : ℝ) * ((1 : ℝ) / ((s : ℝ) ^ 2)) := by
            refine Finset.sum_le_sum fun s hs => ?_
            have hs1 : 1 ≤ s := by have := (Finset.mem_Icc.mp hs).1; omega
            have hc : #((Finset.Icc 1 (X / s ^ 2)).filter isNotP3) ≤ X / s ^ 2 :=
              (Finset.card_filter_le _ _).trans (by simp)
            have hY_le : ((X / s ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) / ((s : ℝ) ^ 2) := by
              rw [le_div_iff₀ (by positivity)]
              exact_mod_cast Nat.div_mul_le_self X (s ^ 2)
            calc (#((Finset.Icc 1 (X / s ^ 2)).filter isNotP3) : ℝ)
                ≤ ((X / s ^ 2 : ℕ) : ℝ) := by exact_mod_cast hc
              _ ≤ (X : ℝ) / ((s : ℝ) ^ 2) := hY_le
              _ = (X : ℝ) * ((1 : ℝ) / ((s : ℝ) ^ 2)) := by ring
        _ = (X : ℝ) * ∑ s ∈ Finset.Icc (S₀ + 1) (Nat.sqrt X), (1 : ℝ) / ((s : ℝ) ^ 2) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (X : ℝ) * (1 / (S₀ : ℝ)) := by
            have := sum_inv_sq_Icc_le (S₀ + 1) (Nat.sqrt X) (by omega) hle
            rw [Nat.add_sub_cancel] at this
            exact mul_le_mul_of_nonneg_left this (by positivity)
        _ = (X : ℝ) / (S₀ : ℝ) := by ring
    -- Bound √(log X) ≤ 2 * S₀
    have hX_lt : X < (2 * S₀) ^ 4 := by
      have h1' : Nat.sqrt X < (S₀ + 1) ^ 2 := by
        have := Nat.lt_succ_sqrt (Nat.sqrt X); nlinarith
      have h2' : X < (Nat.sqrt X + 1) ^ 2 := by
        have := Nat.lt_succ_sqrt X; nlinarith
      have h3' : Nat.sqrt X + 1 ≤ (S₀ + 1) ^ 2 := by omega
      have h4' : S₀ + 1 ≤ 2 * S₀ := by omega
      calc X < (Nat.sqrt X + 1) ^ 2 := h2'
        _ ≤ ((S₀ + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h3' 2
        _ = (S₀ + 1) ^ 4 := by ring
        _ ≤ (2 * S₀) ^ 4 := Nat.pow_le_pow_left h4' 4
    have hlog_le : Real.log (X : ℝ) ≤ 4 * (S₀ : ℝ) ^ 2 := by
      have hS0R : (2 : ℝ) ≤ S₀ := by exact_mod_cast hS0_ge2
      calc Real.log (X : ℝ) ≤ Real.log (((2 * S₀) ^ 4 : ℕ) : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hX_lt.le)
        _ = 4 * Real.log (2 * (S₀ : ℝ)) := by
            push_cast; rw [Real.log_pow]; norm_num
        _ ≤ 4 * (2 * (S₀ : ℝ)) := by
            have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * S₀ by linarith)
            linarith
        _ ≤ 4 * (S₀ : ℝ) ^ 2 := by nlinarith
    have hrt_le : Real.sqrt (Real.log (X : ℝ)) ≤ 2 * (S₀ : ℝ) := by
      calc Real.sqrt (Real.log (X : ℝ)) ≤ Real.sqrt ((2 * (S₀ : ℝ)) ^ 2) :=
            Real.sqrt_le_sqrt (by linarith)
        _ = 2 * (S₀ : ℝ) := Real.sqrt_sq (by positivity)
    calc ∑ s ∈ Finset.Icc (S₀ + 1) (Nat.sqrt X), (#((Finset.Icc 1 (X / s ^ 2)).filter isNotP3) : ℝ)
        ≤ (X : ℝ) / (S₀ : ℝ) := h1
      _ ≤ 2 * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity) hrtX_pos]
          nlinarith
  -- Account for 0 ∈ sumTwoSqSet X
  have hzero : (#(sumTwoSqSet X) : ℝ) ≤ (#((sumTwoSqSet X).erase 0) : ℝ) + 1 := by
    have hnat : #(sumTwoSqSet X) ≤ #((sumTwoSqSet X).erase 0) + 1 := by
      by_cases h0 : 0 ∈ sumTwoSqSet X
      · rw [Finset.card_erase_of_mem h0]
        have : 1 ≤ #(sumTwoSqSet X) := Finset.card_pos.mpr ⟨0, h0⟩
        omega
      · rw [Finset.erase_eq_of_notMem h0]; omega
    exact_mod_cast hnat
  have hone_le : (1 : ℝ) ≤ (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) := by
    rw [one_le_div hrtX_pos]
    calc Real.sqrt (Real.log (X : ℝ)) ≤ Real.sqrt (X : ℝ) :=
          Real.sqrt_le_sqrt (by linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < X)])
      _ ≤ (X : ℝ) := by
          have hXR : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith
  unfold C_twoSq
  calc (#(sumTwoSqSet X) : ℝ)
      ≤ (#((sumTwoSqSet X).erase 0) : ℝ) + 1 := hzero
    _ ≤ (4 * C_notP3 * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) +
          2 * (X : ℝ) / Real.sqrt (Real.log (X : ℝ))) +
          (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) := by
        linarith [hcard_pos, hsplit, hsmall, hlarge, hone_le]
    _ = (4 * C_notP3 + 3) * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) := by ring

/- ### Section 5: Grid construction in `ℝ²` -/

private noncomputable def gridPt (p : ℕ × ℕ) : ℝ² :=
  WithLp.toLp 2 ![(p.1 : ℝ), (p.2 : ℝ)]

private lemma gridPt_injective : Function.Injective gridPt := by
  intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  have h0 : gridPt (a₁, b₁) 0 = gridPt (a₂, b₂) 0 := congrArg (fun v => v 0) h
  have h1 : gridPt (a₁, b₁) 1 = gridPt (a₂, b₂) 1 := congrArg (fun v => v 1) h
  change (a₁ : ℝ) = (a₂ : ℝ) at h0
  change (b₁ : ℝ) = (b₂ : ℝ) at h1
  exact Prod.ext (Nat.cast_injective h0) (Nat.cast_injective h1)

private lemma dist_gridPt (p q : ℕ × ℕ) :
    dist (gridPt p) (gridPt q) =
      Real.sqrt (((Int.natAbs ((p.1 : ℤ) - (q.1 : ℤ)) ^ 2 +
        Int.natAbs ((p.2 : ℤ) - (q.2 : ℤ)) ^ 2 : ℕ) : ℝ)) := by
  have hsq : (dist (gridPt p) (gridPt q)) ^ 2 =
      ((Int.natAbs ((p.1 : ℤ) - (q.1 : ℤ)) ^ 2 +
        Int.natAbs ((p.2 : ℤ) - (q.2 : ℤ)) ^ 2 : ℕ) : ℝ) := by
    rw [dist_eq_norm, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
    simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
    have hg0 : gridPt p 0 - gridPt q 0 = (p.1 : ℝ) - (q.1 : ℝ) := rfl
    have hg1 : gridPt p 1 - gridPt q 1 = (p.2 : ℝ) - (q.2 : ℝ) := rfl
    rw [hg0, hg1]
    have h1 : ((Int.natAbs ((p.1 : ℤ) - (q.1 : ℤ)) : ℝ)) ^ 2 = ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, Int.cast_sub,
        Int.cast_natCast, Int.cast_natCast]
      exact sq_abs _
    have h2 : ((Int.natAbs ((p.2 : ℤ) - (q.2 : ℤ)) : ℝ)) ^ 2 = ((p.2 : ℝ) - (q.2 : ℝ)) ^ 2 := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, Int.cast_sub,
        Int.cast_natCast, Int.cast_natCast]
      exact sq_abs _
    push_cast
    linarith
  rw [← hsq, Real.sqrt_sq dist_nonneg]

private lemma pinnedDistinctDistances_le_card_sumTwoSq {n : ℕ} (hn : 16 ≤ n) :
    Erdos604.pinnedDistinctDistances n ≤ #(sumTwoSqSet (8 * n)) := by
  set m := Nat.sqrt n + 1
  have hm_sq : n ≤ m * m := by
    have hlt : n < m * m := by
      simpa [m, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt n
    exact hlt.le
  set G : Finset ℝ² := (Finset.range m ×ˢ Finset.range m).image gridPt
  have hG_card : #G = m * m := by
    rw [Finset.card_image_of_injective _ gridPt_injective, Finset.card_product, Finset.card_range]
  obtain ⟨A, hAG, hAcard⟩ := Finset.exists_subset_card_eq (hG_card ▸ hm_sq)
  have hsup : A.sup (distinctDistancesFrom A) ≤ #(sumTwoSqSet (8 * n)) := by
    refine Finset.sup_le fun pt hpt => ?_
    obtain ⟨q, hqG, rfl⟩ := Finset.mem_image.mp (hAG hpt)
    simp only [Finset.mem_product, Finset.mem_range] at hqG
    unfold distinctDistancesFrom
    refine (Finset.card_le_card (t := (sumTwoSqSet (8 * n)).image (fun k : ℕ => Real.sqrt (k : ℝ))) ?_).trans
      Finset.card_image_le
    intro d hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    have hxA : x ∈ A :=
      @Finset.mem_of_mem_erase ℝ² (fun a b => Classical.propDecidable (a = b)) _ _ _ hx
    obtain ⟨p, hpG, rfl⟩ := Finset.mem_image.mp (hAG hxA)
    simp only [Finset.mem_product, Finset.mem_range] at hpG
    rw [dist_gridPt]
    set a := Int.natAbs ((p.1 : ℤ) - (q.1 : ℤ))
    set b := Int.natAbs ((p.2 : ℤ) - (q.2 : ℤ))
    have ha : a ≤ m := by omega
    have hb : b ≤ m := by omega
    have hm_le : m ≤ 2 * Nat.sqrt n := by
      have : 4 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
      omega
    have hk_le : a ^ 2 + b ^ 2 ≤ 8 * n := by
      have h1 : a ^ 2 + b ^ 2 ≤ 2 * m ^ 2 := by nlinarith
      have h2 : m ^ 2 ≤ 4 * (Nat.sqrt n) ^ 2 := by nlinarith
      have h3 : (Nat.sqrt n) ^ 2 ≤ n := by
        have := Nat.sqrt_le n; nlinarith
      nlinarith
    refine Finset.mem_image.mpr ⟨a ^ 2 + b ^ 2, ?_, rfl⟩
    simp only [sumTwoSqSet, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.zero_le _, hk_le⟩, ⟨a, b, rfl⟩⟩
  have hmem : A.sup (distinctDistancesFrom A) ∈
      {k : ℕ | ∃ B : Finset ℝ², #B = n ∧ B.sup (distinctDistancesFrom B) = k} :=
    ⟨A, hAcard, rfl⟩
  exact le_trans (Nat.sInf_le hmem) hsup

end Erdos604GridUpperBound

open Erdos604GridUpperBound in
theorem OMA.solution : type_of% @Erdos604.erdos_604.variants.grid_upper_bound := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨8 * C_twoSq, Filter.eventually_atTop.mpr ⟨16, fun n hn => ?_⟩⟩
  have h1 : (Erdos604.pinnedDistinctDistances n : ℝ) ≤ (#(sumTwoSqSet (8 * n)) : ℝ) := by
    exact_mod_cast pinnedDistinctDistances_le_card_sumTwoSq hn
  have h2 := card_sumTwoSqSet_le (show 16 ≤ 8 * n by omega)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlog8n : Real.log (n : ℝ) ≤ Real.log ((8 * n : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (by omega : n ≤ 8 * n))
  have hrtn_pos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlogn
  have hrt8n : Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log ((8 * n : ℕ) : ℝ)) :=
    Real.sqrt_le_sqrt hlog8n
  have h3 : C_twoSq * ((8 * n : ℕ) : ℝ) / Real.sqrt (Real.log ((8 * n : ℕ) : ℝ)) ≤
      (8 * C_twoSq) * ((n : ℝ) / Real.sqrt (Real.log (n : ℝ))) := by
    have hCpos := C_twoSq_pos
    have hnum : C_twoSq * ((8 * n : ℕ) : ℝ) = (8 * C_twoSq) * (n : ℝ) := by push_cast; ring
    rw [show (8 * C_twoSq) * ((n : ℝ) / Real.sqrt (Real.log (n : ℝ))) =
        ((8 * C_twoSq) * (n : ℝ)) / Real.sqrt (Real.log (n : ℝ)) by ring, ← hnum]
    exact div_le_div_of_nonneg_left (by positivity) hrtn_pos hrt8n
  have hnn_lhs : 0 ≤ (Erdos604.pinnedDistinctDistances n : ℝ) := Nat.cast_nonneg _
  have hnn_rhs : 0 ≤ (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by positivity
  rw [Real.norm_of_nonneg hnn_lhs, Real.norm_of_nonneg hnn_rhs]
  exact (h1.trans h2).trans h3
