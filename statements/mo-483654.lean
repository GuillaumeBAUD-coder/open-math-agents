import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# An inequality related to Problem 10210 AMM 1992 No. 3

Source: https://mathoverflow.net/questions/483654
Credit: @etaubman

The source asks for every nonnegative square real matrix `A`:
`N² 1ᵀ Aᵀ A Aᵀ 1 ≥ (1ᵀ A 1)³`, where `1` is the all-ones vector.
For any matrix `B`, the contraction `1ᵀ B 1` is its sum of entries, so the
two contractions below are written as double finite sums. No symmetry,
strict positivity, or normalization is assumed. The empty matrix is
included, with both sides zero.

This is the finite matrix problem stated first in the source. The integral
AMM problem quoted there supplies background.
-/

open scoped BigOperators Matrix

namespace OMA.S_mo_483654

theorem main : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    (∀ i j, 0 ≤ A i j) →
    (∑ i, ∑ j, A i j) ^ 3 ≤
      (n : ℝ) ^ 2 * (∑ i, ∑ j, (Aᵀ * A * Aᵀ) i j) := by
  sorry

end OMA.S_mo_483654
