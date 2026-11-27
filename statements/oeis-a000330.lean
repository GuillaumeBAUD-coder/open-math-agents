import Mathlib

/-!
# A000330: Square pyramidal numbers: a(n) = 0^2 + 1^2 + 2^2 + ... + n^2 = n*(n+1)*(2*n+1)/6.

Source: https://oeis.org/A000330
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a000330

def IsGeneralizedPyramidal (r : ℕ) (x : ℤ) : Prop :=
  ∃ n : ℤ, 6 * x = n * (n + 1) * (((r : ℤ) - 2) * n - (r : ℤ) + 5)

def IsSumOfThreeGeneralizedPyramidal (r : ℕ) (z : ℤ) : Prop :=
  ∃ x y w : ℤ, IsGeneralizedPyramidal r x ∧ IsGeneralizedPyramidal r y ∧
    IsGeneralizedPyramidal r w ∧ z = x + y + w

theorem main : (∀ z : ℤ, IsSumOfThreeGeneralizedPyramidal 4 z) ∧
    ∀ r : ℕ, 3 ≤ r → ∀ z : ℤ, IsSumOfThreeGeneralizedPyramidal r z := by
  sorry

end OMA.S_oeis_a000330
