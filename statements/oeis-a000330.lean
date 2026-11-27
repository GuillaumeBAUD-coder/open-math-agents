import Mathlib

/-!
# A000330: Square pyramidal numbers.

Source: https://oeis.org/A000330
Credit: @rabdelaal

`a n = n*(n+1)*(2*n+1)/6`, the sum `0^2 + ... + n^2` (OEIS A000330). Generalized square
pyramidal numbers allow negative arguments of the same polynomial.

OEIS A000330 records the conjecture that every integer is a sum of three generalized
square pyramidal numbers.
-/

namespace OMA.S_oeis_a000330

/-- The square pyramidal polynomial, extended to all integers (the "generalized"
square pyramidal numbers). -/
def pyr (n : ℤ) : ℤ := n * (n + 1) * (2 * n + 1) / 6

/-- The conjecture recorded in OEIS A000330: every integer is a sum of three generalized
square pyramidal numbers. -/
theorem main : ∀ m : ℤ, ∃ x y z : ℤ, m = pyr x + pyr y + pyr z := by
  sorry

end OMA.S_oeis_a000330
