import Mathlib

/-!
# A203235: (n-1)-st elementary symmetric function of the first n terms of the periodic sequence (1,1,1,3,1,1,1,3,...).

Source: https://oeis.org/A203235
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 2, 3, 10, 13, 16, 19, 60, 69, 78, ...
It is defined as in the name of the entry: a(n) is the (n-1)-st elementary symmetric function of
x(1), ..., x(n), where x is the periodic sequence 1, 1, 1, 3, 1, 1, 1, 3, .... Below the terms are indexed from 0
(x 0 is the first term) and Mathlib's Multiset.esymm is used.

Conjecture (R. J. Mathar, Oct 15 2013): a(n) = 6*a(n-4)-9*a(n-8) with G.f. x*(1+2*x+3*x^2+10*x^3+7*x^4+4*x^5+x^6) / ( (-1+3*x^4)^2 ).
The recurrence involves a(n-8) and the offset is 1, so it is stated for n >= 9. The generating
function is the series Sum_(n>=1) a(n) x^n, and the claim is stated as the identity
G(x) * denominator = numerator between formal power series over the integers.
-/

namespace OMA.S_oeis_a203235

open PowerSeries

/-- The periodic sequence, indexed from 0. -/
def x (i : ℕ) : ℤ := if i % 4 = 3 then 3 else 1

/-- A203235: the (n-1)-st elementary symmetric function of the first n terms of x. -/
def a (n : ℕ) : ℤ := ((Multiset.range n).map x).esymm (n - 1)

/-- The conjectured recurrence and generating function for A203235. -/
theorem main :
    (∀ n : ℕ, 9 ≤ n → a n = 6 * a (n - 4) - 9 * a (n - 8)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (-1 + 3 * X ^ 4) ^ 2
      = X + 2 * X ^ 2 + 3 * X ^ 3 + 10 * X ^ 4 + 7 * X ^ 5 + 4 * X ^ 6 + X ^ 7 := by
  sorry

end OMA.S_oeis_a203235
