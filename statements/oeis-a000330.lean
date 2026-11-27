import Mathlib

/-!
# A000330: Square pyramidal numbers: a(n) = 0^2 + 1^2 + 2^2 + ... + n^2 = n*(n+1)*(2*n+1)/6.

Source: https://oeis.org/A000330
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a000330

/-- Square pyramidal number with an integer index: n(n+1)(2n+1)/6 (always an integer; the
division is exact). Negative indices give the "generalized" ones. A000330 is the case n >= 0. -/
def pyr (n : ℤ) : ℤ := n * (n + 1) * (2 * n + 1) / 6

/-- Conjecture (Altug Alkan, 2020): every integer is a sum of three generalized square
pyramidal numbers, i.e. of three values `pyr x` with `x : ℤ`. -/
theorem main : ∀ m : ℤ, ∃ x y z : ℤ, m = pyr x + pyr y + pyr z := by
  sorry

end OMA.S_oeis_a000330
