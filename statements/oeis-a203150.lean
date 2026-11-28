import Mathlib

/-!
# A203150: (n-1)-st elementary symmetric function of the first n terms of (1,2,1,2,1,2,1,2,1,2,...)=A000034.

Source: https://oeis.org/A203150
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 3, 5, 12, 16, 36, 44, 96, 112, 240, ...
It is defined as in the name of the entry: a(n) is the (n-1)-st elementary symmetric function of
x(1), ..., x(n), where x is the periodic sequence 1, 2, 1, 2, ... (A000034). Below the terms of x
are indexed from 0 (x 0 = 1 is the first term) and Mathlib's Multiset.esymm is used.

Conjecture (Bruno Berselli, Jan 03 2011):
a(n) = (6*r*n+(1+3*(1-r)*n)*(1-(-1)^n))*r^(n-1)/8, where r=sqrt(2).
The offset is 1, so it is stated for n >= 1, as an identity between real numbers.
-/

namespace OMA.S_oeis_a203150

/-- The periodic sequence 1, 2, 1, 2, ... (A000034), indexed from 0. -/
def x (i : ℕ) : ℤ := if i % 2 = 0 then 1 else 2

/-- A203150: the (n-1)-st elementary symmetric function of the first n terms of x. -/
def a (n : ℕ) : ℤ := ((Multiset.range n).map x).esymm (n - 1)

/-- The conjectured closed form for A203150, with r = sqrt(2). -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℝ) = (6 * Real.sqrt 2 * (n : ℝ)
        + (1 + 3 * (1 - Real.sqrt 2) * (n : ℝ)) * (1 - (-1 : ℝ) ^ n))
      * Real.sqrt 2 ^ (n - 1) / 8 := by
  sorry

end OMA.S_oeis_a203150
