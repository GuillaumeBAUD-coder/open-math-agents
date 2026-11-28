import OMAStatements.S_oeis_a020964
import Mathlib

/-!
The sum defining each term is finite because exponents at most minus two
have zero floor. Consecutive terms therefore differ by one floor of
a power of the silver ratio. Adding the power of the algebraic conjugate
gives an integer trace satisfying a second-order recursion. From exponent
two onward the conjugate changes the floor by a parity term of period two.
These recursions give the proposed denominator. The first seven
coefficients of the product give the numerator.
-/

namespace OMA.A020964

open PowerSeries S_oeis_a020964

noncomputable def u : ℝ := 1 + Real.sqrt 2
noncomputable def v : ℝ := 1 - Real.sqrt 2
noncomputable def b (n : ℤ) : ℤ := ⌊3 * u ^ n⌋

/-- Rational bounds suffice for all exceptional floors. -/
lemma sqrt_bounds : (7 : ℝ) / 5 < Real.sqrt 2 ∧ Real.sqrt 2 < 3 / 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

/-- All sufficiently negative exponents contribute zero. -/
lemma b_vanish (n : ℤ) (hn : n ≤ -2) : b n = 0 := by
  have hu : 2 < u := by unfold u; linarith [sqrt_bounds.1]
  have hpow : u ^ n ≤ u ^ (-2 : ℤ) := zpow_le_zpow_right₀ (by linarith) hn
  have hsmall : 3 * u ^ (-2 : ℤ) < 1 := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by rfl, zpow_neg]
    change 3 * (u ^ (2 : ℕ))⁻¹ < 1
    have hpos : 0 < u := by linarith
    rw [← div_eq_mul_inv, div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg (u - 2)]
  apply Int.floor_eq_iff.mpr
  constructor
  · push_cast
    positivity
  · norm_num
    linarith

/-- The defining infinite sum has finite support. -/
lemma summable_terms (n : ℕ) : Summable (fun k : ℕ => b ((n : ℤ) - ((k : ℤ) + 1))) := by
  apply summable_of_hasFiniteSupport
  apply (Set.finite_Iic n).subset
  intro k hk
  by_contra hkn
  apply hk
  apply b_vanish
  have hlt : n < k := lt_of_not_ge hkn
  omega

/-- Separating the first term gives the consecutive difference formula. -/
lemma a_succ (n : ℕ) : a (n + 1) = b n + a n := by
  change (∑' k : ℕ, b (((n + 1 : ℕ) : ℤ) - ((k : ℤ) + 1))) =
    b n + ∑' k : ℕ, b ((n : ℤ) - ((k : ℤ) + 1))
  rw [(summable_terms (n + 1)).tsum_eq_zero_add]
  push_cast
  congr 1
  · congr 1
    ring
  · congr 1
    ext k
    congr 1
    ring

/-- The integer trace is the sum of the powers at the two quadratic roots. -/
def trace : ℕ → ℤ
  | 0 => 6
  | 1 => 6
  | n + 2 => 2 * trace (n + 1) + trace n

/-- Both roots satisfy the same quadratic identity, which proves the trace formula. -/
lemma trace_cast (n : ℕ) : (trace n : ℝ) = 3 * (u ^ n + v ^ n) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hu : u ^ 2 = 2 * u + 1 := by unfold u; nlinarith
  have hv : v ^ 2 = 2 * v + 1 := by unfold v; nlinarith
  induction n using Nat.twoStepInduction with
  | zero => norm_num [trace]
  | one => norm_num [trace, u, v]
  | more n h₀ h₁ =>
    rw [trace]
    push_cast
    rw [h₀, h₁, pow_add u n 2, pow_add v n 2, hu, hv, pow_succ, pow_succ]
    ring

/-- The conjugate contribution has absolute value less than one from exponent two. -/
lemma conjugate_small (n : ℕ) (hn : 2 ≤ n) : |3 * v ^ n| < 1 := by
  have hv : v < 0 := by unfold v; linarith [sqrt_bounds.1]
  have hbound : |v| ≤ 1 / 2 := by
    rw [abs_of_neg hv]
    unfold v
    linarith [sqrt_bounds.2]
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
  have h₂ := pow_le_pow_left₀ (abs_nonneg v) hbound 2
  have hk := pow_le_one₀ (abs_nonneg v) (by linarith : |v| ≤ 1) (n := k)
  rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), pow_add]
  calc
    3 * (|v| ^ 2 * |v| ^ k) ≤ 3 * (|v| ^ 2 * 1) := by gcongr
    _ < 1 := by
      norm_num only [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num] at h₂
      linarith

/-- Rounding the trace subtracts one precisely at even exponents. -/
lemma b_formula (n : ℕ) (hn : 2 ≤ n) :
    b n = trace n - (if n % 2 = 0 then 1 else 0) := by
  have hv : v < 0 := by unfold v; linarith [sqrt_bounds.1]
  have hsmall := abs_lt.mp (conjugate_small n hn)
  have ht := trace_cast n
  rw [b, zpow_natCast]
  by_cases he : n % 2 = 0
  · have hp : 0 < v ^ n := (Nat.even_iff.mpr he).pow_pos hv.ne
    simp only [he, if_true]
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith [mul_pos (by norm_num : (0 : ℝ) < 3) hp]
  · have hp : v ^ n < 0 := (Nat.odd_iff.mpr (by omega)).pow_neg hv
    simp only [he, if_false, sub_zero]
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith [mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 3) hp]

/-- Combining the quadratic recursion with period two gives the difference recursion. -/
lemma b_recurrence (n : ℕ) (hn : 2 ≤ n) :
    b (↑(n + 4) : ℤ) - 2 * b (↑(n + 3) : ℤ) - 2 * b (↑(n + 2) : ℤ) +
      2 * b (↑(n + 1) : ℤ) + b (n : ℤ) = 0 := by
  rw [b_formula (n + 4) (by omega), b_formula (n + 3) (by omega),
    b_formula (n + 2) (by omega), b_formula (n + 1) (by omega), b_formula n hn]
  rw [show (n + 4) % 2 = n % 2 by omega,
    show (n + 3) % 2 = (n + 1) % 2 by omega, show (n + 2) % 2 = n % 2 by omega]
  rw [trace.eq_3 (n + 2), trace.eq_3 (n + 1), trace.eq_3 n]
  ring

/-- Substituting the consecutive differences gives the required sequence recursion. -/
lemma recurrence (n : ℕ) (hn : 6 < n) :
    a n = 3 * a (n - 1) - 4 * a (n - 3) + a (n - 4) + a (n - 5) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have h := b_recurrence k (by omega)
  have hb (j : ℕ) : b (j : ℤ) = a (j + 1) - a j := by rw [a_succ]; ring
  simp only [hb] at h
  simp only [show ∀ k : ℕ, k + 5 - 1 = k + 4 by omega,
    show ∀ k : ℕ, k + 5 - 3 = k + 2 by omega,
    show ∀ k : ℕ, k + 5 - 4 = k + 1 by omega,
    show ∀ k : ℕ, k + 5 - 5 = k by omega]
  linarith

/-- The exceptional initial floors, followed by the first trace-formula floors. -/
lemma initial_floors :
    b (-1) = 1 ∧ b 0 = 3 ∧ b 1 = 7 ∧ b 2 = 17 ∧ b 3 = 42 ∧ b 4 = 101 ∧ b 5 = 246 := by
  have hu : (12 : ℝ) / 5 < u ∧ u < 5 / 2 := by
    unfold u
    constructor <;> linarith [sqrt_bounds.1, sqrt_bounds.2]
  have hneg : b (-1) = 1 := by
    rw [b, zpow_neg_one, ← div_eq_mul_inv]
    apply Int.floor_eq_iff.mpr
    have hpos : 0 < u := by linarith [hu.1]
    constructor
    · norm_num only [Int.cast_one]
      apply (le_div_iff₀ hpos).2
      linarith [hu.2]
    · norm_num only [Int.cast_one]
      apply (div_lt_iff₀ hpos).2
      linarith [hu.1]
  have hzero : b 0 = 3 := by norm_num [b]
  have hone : b 1 = 7 := by
    rw [b, zpow_one, Int.floor_eq_iff]
    norm_num
    constructor <;> linarith [hu.1, hu.2]
  refine ⟨hneg, hzero, hone, ?_, ?_, ?_, ?_⟩
  · have h := b_formula 2 (by decide)
    norm_num [trace] at h
    exact h
  · have h := b_formula 3 (by decide)
    norm_num [trace] at h
    exact h
  · have h := b_formula 4 (by decide)
    norm_num [trace] at h
    exact h
  · have h := b_formula 5 (by decide)
    norm_num [trace] at h
    exact h

/-- At index zero only the floor at exponent minus one survives. -/
lemma a_zero : a 0 = 1 := by
  change (∑' k : ℕ, b (((0 : ℕ) : ℤ) - ((k : ℤ) + 1))) = 1
  rw [(summable_terms 0).tsum_eq_zero_add]
  have hz : (fun k : ℕ => b (((0 : ℕ) : ℤ) - (((k + 1 : ℕ) : ℤ) + 1))) = 0 := by
    funext k
    apply b_vanish
    omega
  rw [hz]
  change b (((0 : ℕ) : ℤ) - (((0 : ℕ) : ℤ) + 1)) + (∑' _ : ℕ, (0 : ℤ)) = 1
  simpa using initial_floors.1

/-- The product by the claimed denominator has the given numerator. -/
lemma series_product :
    mk a * (1 - C 3 * X + C 4 * X ^ 3 - X ^ 4 - X ^ 5) =
      1 + X - X ^ 2 - X ^ 3 + X ^ 4 + X ^ 6 := by
  have h₁ : mk a * (C 3 * X) = C 3 * (mk a * X ^ 1) := by ring
  have h₃ : mk a * (C 4 * X ^ 3) = C 4 * (mk a * X ^ 3) := by ring
  obtain ⟨_, b₀, b₁, b₂, b₃, b₄, b₅⟩ := initial_floors
  have a₁ : a 1 = 4 := by norm_num [a_succ 0, b₀, a_zero]
  have a₂ : a 2 = 11 := by norm_num [a_succ 1, b₁, a₁]
  have a₃ : a 3 = 28 := by norm_num [a_succ 2, b₂, a₂]
  have a₄ : a 4 = 70 := by norm_num [a_succ 3, b₃, a₃]
  have a₅ : a 5 = 171 := by norm_num [a_succ 4, b₄, a₄]
  have a₆ : a 6 = 417 := by norm_num [a_succ 5, b₅, a₅]
  ext n
  simp only [mul_sub, mul_add, mul_one, h₁, h₃, map_add, map_sub, coeff_C_mul,
    coeff_mul_X_pow', coeff_X_pow, coeff_X, coeff_one, coeff_mk]
  by_cases hn : 6 < n
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega), if_pos (show 5 ≤ n by omega),
      if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 6 by omega)]
    linarith [recurrence n hn]
  · interval_cases n <;> norm_num [a_zero, a₁, a₂, a₃, a₄, a₅, a₆]

end OMA.A020964

open PowerSeries OMA.S_oeis_a020964 in
theorem OMA.solution : type_of% @OMA.S_oeis_a020964.main := by
  refine ⟨OMA.A020964.recurrence, ?_⟩
  let d : PowerSeries ℤ := 1 - C 3 * X + C 4 * X ^ 3 - X ^ 4 - X ^ 5
  have hd : constantCoeff d = ↑(1 : ℤˣ) := by simp [d]
  have hprod := OMA.A020964.series_product
  change mk a = invOfUnit d 1 * _
  rw [← hprod, mul_comm (mk a) d, ← mul_assoc, invOfUnit_mul d 1 hd, one_mul]
