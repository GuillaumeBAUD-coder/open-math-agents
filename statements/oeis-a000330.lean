import Mathlib

/-!
# A000330: every integer is a sum of three generalized square pyramidal numbers

Source: https://oeis.org/A000330
Credit: @caa1982

The square pyramidal numbers are $a(n) = 0^2 + 1^2 + \cdots + n^2 = n(n+1)(2n+1)/6$ (OEIS A000330).
Conjecture (Altug Alkan, Jul 30 2020): every integer can be represented as a sum of three
generalized square pyramidal numbers, where "generalized" means negative indices are included,
i.e. the values $n(n+1)(2n+1)/6$ for all integers $n$ (for example $-1, -5, -14$ for
$n = -2, -3, -4$). Repetitions among the three summands are allowed, as usual for such
representations.

The quotient $n(n+1)(2n+1)/6$ is exact for every integer $n$, so integer division below loses
nothing. Some representations need very large indices (for instance
$73 = a(-287) + a(-146) + a(298)$, i.e. $-7838831 - 1026745 + 8865649$).
-/

namespace OMA.S_oeis_a000330

/-- The generalized square pyramidal number $n(n+1)(2n+1)/6$ for an integer index `n`. -/
def genSquarePyramidal (n : ℤ) : ℤ := n * (n + 1) * (2 * n + 1) / 6

/-- Conjecture: every integer is the sum of three generalized square pyramidal numbers. -/
theorem main : ∀ m : ℤ, ∃ x y z : ℤ,
    m = genSquarePyramidal x + genSquarePyramidal y + genSquarePyramidal z := by
  sorry

end OMA.S_oeis_a000330
