import Mathlib

/-!
# A211439: Number of ordered triples (w,x,y) with all terms in {-n,...,0,...,n} and w+3x+3y=0.

Source: https://oeis.org/A211439
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 3, 5, 19, 25, 31, 59, 69, 79, 121, ...
It is defined as in the name of the entry: the number of triples (w, x, y) of integers, each between
-n and n, with w + 3x + 3y = 0.

Conjectures from Colin Barker, May 15 2017:
G.f.: (1 + 2*x + 2*x^2 + 12*x^3 + 2*x^4 + 2*x^5 + x^6) / ((1 - x)^3*(1 + x + x^2)^2).
a(n) = a(n-1) + 2*a(n-3) - 2*a(n-4) - a(n-6) + a(n-7) for n>6.
The generating function is the series Sum_(n>=0) a(n) x^n, and the claim is stated as the identity
G(x) * denominator = numerator between formal power series over the integers.
-/

namespace OMA.S_oeis_a211439

open PowerSeries

/-- A211439: the number of (w, x, y) with all terms in -n..n and w + 3x + 3y = 0. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun t => t.1 + 3 * t.2.1 + 3 * t.2.2 = 0)).card

/-- The conjectured generating function and recurrence for A211439. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X + X ^ 2) ^ 2)
      = 1 + 2 * X + 2 * X ^ 2 + 12 * X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + X ^ 6 ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = a (n - 1) + 2 * a (n - 3) - 2 * a (n - 4) - a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a211439
