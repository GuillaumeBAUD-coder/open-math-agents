import Mathlib

namespace OMA.S_oeis_a019429

/-- Remainders of the simple continued fraction algorithm (Gauss map) starting at `x : ℝ`:
`cfRem x 0 = x` and `cfRem x (n + 1) = (cfRem x n - ⌊cfRem x n⌋)⁻¹`. -/
noncomputable def cfRem (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => (cfRem x n - (⌊cfRem x n⌋ : ℝ))⁻¹

/-- Simple continued fraction partial quotients of `x : ℝ`: `cfCoeff x n = ⌊cfRem x n⌋`. -/
noncomputable def cfCoeff (x : ℝ) (n : ℕ) : ℤ :=
  ⌊cfRem x n⌋

/-- OEIS A019429: Continued fraction expansion of `tan(1/6)` (`0, 5, 1, 16, 1, 28, 1, 40, ...`).
Conjectures (Colin Barker / Peter Bala):
1. `a(0) = 0`, `a(1) = 5`, and for all `n ≥ 1`, `a(2n) = 1` and `a(2n + 1) = 12 * n + 4`.
2. Equivalently, for all `n ≥ 2`, `2 * a(n) = -1 + 3 * (-1)^n - 6 * (-1 + (-1)^n) * n`.
3. For all `n ≥ 6`, `a(n) = 2 * a(n - 2) - a(n - 4)`. -/
theorem main :
    cfCoeff (Real.tan (1 / 6)) 0 = 0 ∧
    cfCoeff (Real.tan (1 / 6)) 1 = 5 ∧
    (∀ n : ℕ, 1 ≤ n → cfCoeff (Real.tan (1 / 6)) (2 * n) = 1) ∧
    (∀ n : ℕ, 1 ≤ n → cfCoeff (Real.tan (1 / 6)) (2 * n + 1) = 12 * (n : ℤ) + 4) ∧
    (∀ n : ℕ, 2 ≤ n →
      2 * cfCoeff (Real.tan (1 / 6)) n =
        -1 + 3 * (-1 : ℤ) ^ n - 6 * (-1 + (-1 : ℤ) ^ n) * (n : ℤ)) ∧
    (∀ n : ℕ, 6 ≤ n →
      cfCoeff (Real.tan (1 / 6)) n =
        2 * cfCoeff (Real.tan (1 / 6)) (n - 2) - cfCoeff (Real.tan (1 / 6)) (n - 4)) := by
  sorry

end OMA.S_oeis_a019429
