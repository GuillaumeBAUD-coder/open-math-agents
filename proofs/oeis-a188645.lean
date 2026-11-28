import OMAStatements.S_oeis_a188645
import Mathlib

/-!
# OEIS A188645: `(kⁿ + k⁻ⁿ)/2` is an integer for `k = (√(x² + y) + x)²`, `y = ±1`

Put `s = √(x² + y)`, so `s² = x² + y` and `(s + x)(s - x) = y`. Hence

  `k = (s + x)²`,  `k⁻¹ = (s - x)²`  (their product is `y² = 1`),
  `k + k⁻¹ = 2 s² + 2 x² = 2 (2x² + y)`.

So `c(n) = (kⁿ + k⁻ⁿ)/2` satisfies `c(0) = 1`, `c(1) = 2x² + y` and
`c(n+2) = (k + k⁻¹) c(n+1) - c(n) = 2 (2x² + y) c(n+1) - c(n)`, and is an integer by induction.
-/

open OMA.S_oeis_a188645

namespace OMA.A188645

/-- `k ≠ 0` and `k + k⁻¹ = 2 (2x² + y)`. -/
lemma k_facts (x y : ℤ) (hx : 1 ≤ x) (hy : y = 1 ∨ y = -1) :
    k x y ≠ 0 ∧ k x y + (k x y)⁻¹ = 2 * (2 * (x : ℝ) ^ 2 + y) := by
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hnn : (0 : ℝ) ≤ (x : ℝ) ^ 2 + y := by
    rcases hy with rfl | rfl <;> push_cast <;> nlinarith
  have hy2 : (y : ℝ) ^ 2 = 1 := by
    rcases hy with rfl | rfl <;> norm_num
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt ((x : ℝ) ^ 2 + y) := ⟨_, rfl⟩
  have hs2 : s ^ 2 = (x : ℝ) ^ 2 + y := by rw [hs]; exact Real.sq_sqrt hnn
  have hk : k x y = (s + x) ^ 2 := by unfold k; rw [hs]
  have hprod : (s + x) ^ 2 * (s - x) ^ 2 = 1 := by
    have h1 : (s + x) * (s - x) = y := by nlinarith
    calc (s + x) ^ 2 * (s - x) ^ 2 = ((s + x) * (s - x)) ^ 2 := by ring
      _ = 1 := by rw [h1, hy2]
  rw [hk]
  refine ⟨left_ne_zero_of_mul_eq_one hprod, ?_⟩
  rw [inv_eq_of_mul_eq_one_right hprod]
  nlinarith

end OMA.A188645

open OMA.A188645 in
theorem OMA.solution : type_of% @OMA.S_oeis_a188645.main := by
  intro x y hx hy n
  obtain ⟨hK, hsum⟩ := k_facts x y hx hy
  have hmul : k x y * (k x y)⁻¹ = 1 := mul_inv_cancel₀ hK
  have key : ∀ n : ℕ, ∃ m : ℤ, (k x y ^ n + (k x y)⁻¹ ^ n) / 2 = m := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => exact ⟨1, by norm_num⟩
    | one =>
      refine ⟨2 * x ^ 2 + y, ?_⟩
      rw [pow_one, pow_one, hsum]
      push_cast
      ring
    | more n h0 h1 =>
      obtain ⟨m0, hm0⟩ := h0
      obtain ⟨m1, hm1⟩ := h1
      refine ⟨2 * (2 * x ^ 2 + y) * m1 - m0, ?_⟩
      have e : k x y ^ (n + 2) + (k x y)⁻¹ ^ (n + 2)
          = (k x y + (k x y)⁻¹) * (k x y ^ (n + 1) + (k x y)⁻¹ ^ (n + 1))
            - (k x y * (k x y)⁻¹) * (k x y ^ n + (k x y)⁻¹ ^ n) := by ring
      push_cast
      rw [← hm0, ← hm1, e, hsum, hmul]
      ring
  obtain ⟨m, hm⟩ := key n
  refine ⟨m, ?_⟩
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  exact hm
