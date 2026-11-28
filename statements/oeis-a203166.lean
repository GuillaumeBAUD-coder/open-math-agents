import Mathlib

/-!
# A203166: (n-1)-st elementary symmetric function of the first n terms of (1,2,3,4,5,1,2,3,4,5,...)=A010884.

Source: https://oeis.org/A203166
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 3, 11, 50, 274, 394, 908, 2964, 12576, 65760, ...
It is defined as in the name of the entry: a(n) is the (n-1)-st elementary symmetric function of
x(1), ..., x(n), where x is the periodic sequence 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, ... (A010884). Below the terms are indexed from 0
(x 0 is the first term) and Mathlib's Multiset.esymm is used.

Conjecture (R. J. Mathar, Jul 02 2013): a(n) = 240*a(n-5) -14400*a(n-10) with G.f. x*(1+3*x+11*x^2+50*x^3+274*x^4+154*x^5+188*x^6+324*x^7+576*x^8) / (-1+120*x^5)^2.
The recurrence involves a(n-10) and the offset is 1, so it is stated for n >= 11. The generating
function is the series Sum_(n>=1) a(n) x^n, and the claim is stated as the identity
G(x) * denominator = numerator between formal power series over the integers.
-/

namespace OMA.S_oeis_a203166

open PowerSeries

/-- The periodic sequence, indexed from 0. -/
def x (i : ℕ) : ℤ := ((i % 5 : ℕ) : ℤ) + 1

/-- A203166: the (n-1)-st elementary symmetric function of the first n terms of x. -/
def a (n : ℕ) : ℤ := ((Multiset.range n).map x).esymm (n - 1)

/-- The conjectured recurrence and generating function for A203166. -/
theorem main :
    (∀ n : ℕ, 11 ≤ n → a n = 240 * a (n - 5) - 14400 * a (n - 10)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (-1 + 120 * X ^ 5) ^ 2
      = X + 3 * X ^ 2 + 11 * X ^ 3 + 50 * X ^ 4 + 274 * X ^ 5 + 154 * X ^ 6 + 188 * X ^ 7 + 324 * X ^ 8 + 576 * X ^ 9 := by
  sorry

end OMA.S_oeis_a203166
