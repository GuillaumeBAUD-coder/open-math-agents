import Mathlib

/-!
# A203231: (n-1)-st elementary symmetric function of the first n terms of the periodic sequence (3,1,3,1,3,1,3,1,...).

Source: https://oeis.org/A203231
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 4, 15, 24, 81, 108, 351, 432, 1377, 1620, ...
It is defined as in the name of the entry: a(n) is the (n-1)-st elementary symmetric function of
x(1), ..., x(n), where x is the periodic sequence 3, 1, 3, 1, .... Below the terms are indexed from 0
(x 0 is the first term) and Mathlib's Multiset.esymm is used.

Conjecture (R. J. Mathar, Oct 15 2013): a(n) = 6*a(n-2)-9*a(n-4) with G.f. x*(1+4*x+9*x^2) / (-1+3*x^2)^2.
The recurrence involves a(n-4) and the offset is 1, so it is stated for n >= 5. The generating
function is the series Sum_(n>=1) a(n) x^n, and the claim is stated as the identity
G(x) * denominator = numerator between formal power series over the integers.
-/

namespace OMA.S_oeis_a203231

open PowerSeries

/-- The periodic sequence, indexed from 0. -/
def x (i : ℕ) : ℤ := if i % 2 = 0 then 3 else 1

/-- A203231: the (n-1)-st elementary symmetric function of the first n terms of x. -/
def a (n : ℕ) : ℤ := ((Multiset.range n).map x).esymm (n - 1)

/-- The conjectured recurrence and generating function for A203231. -/
theorem main :
    (∀ n : ℕ, 5 ≤ n → a n = 6 * a (n - 2) - 9 * a (n - 4)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (-1 + 3 * X ^ 2) ^ 2
      = X + 4 * X ^ 2 + 9 * X ^ 3 := by
  sorry

end OMA.S_oeis_a203231
