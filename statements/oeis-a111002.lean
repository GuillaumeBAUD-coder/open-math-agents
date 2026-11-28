import Mathlib

/-!
# A111002: a(n) = gcd(f(n), f(n+1)) where f(n) = n^4 + n^2 + 1.

Source: https://oeis.org/A111002
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 3, 7, 91, 21, 31, 43, 57, 73, 91, 777, 133, ...
It is defined exactly as in the name of the entry.

Conjectures from Colin Barker, Oct 06 2015:
  a(n) = 3*a(n-7) - 3*a(n-14) + a(n-21) for n > 20.
  G.f.: -(x^20 + 3*x^19 + 7*x^18 + 91*x^17 + 21*x^16 + 31*x^15 + 43*x^14 + 54*x^13 + 64*x^12
          + 70*x^11 + 504*x^10 + 70*x^9 + 64*x^8 + 54*x^7 + 43*x^6 + 31*x^5 + 21*x^4 + 91*x^3
          + 7*x^2 + 3*x + 1) / ((x - 1)^3*(x^6 + x^5 + x^4 + x^3 + x^2 + x + 1)^3).
Both are stated; the second one as the identity G(x) * denominator = numerator between formal
power series over the integers, where G is the generating function of the sequence.
-/

namespace OMA.S_oeis_a111002

open PowerSeries

/-- f(n) = n^4 + n^2 + 1. -/
def f (n : ℕ) : ℕ := n ^ 4 + n ^ 2 + 1

/-- A111002: a(n) = gcd(f(n), f(n+1)). -/
def a (n : ℕ) : ℕ := Nat.gcd (f n) (f (n + 1))

/-- Colin Barker's conjectured recurrence and generating function for A111002. -/
theorem main :
    (∀ n : ℕ, 20 < n → (a n : ℤ) = 3 * a (n - 7) - 3 * a (n - 14) + a (n - 21)) ∧
    PowerSeries.mk (fun n => (a n : ℤ))
        * ((X - 1) ^ 3 * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 3)
      = -(X ^ 20 + 3 * X ^ 19 + 7 * X ^ 18 + 91 * X ^ 17 + 21 * X ^ 16 + 31 * X ^ 15
          + 43 * X ^ 14 + 54 * X ^ 13 + 64 * X ^ 12 + 70 * X ^ 11 + 504 * X ^ 10
          + 70 * X ^ 9 + 64 * X ^ 8 + 54 * X ^ 7 + 43 * X ^ 6 + 31 * X ^ 5
          + 21 * X ^ 4 + 91 * X ^ 3 + 7 * X ^ 2 + 3 * X + 1) := by
  sorry

end OMA.S_oeis_a111002
