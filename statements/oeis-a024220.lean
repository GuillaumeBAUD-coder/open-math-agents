import Mathlib

/-!
# A024220: a(n) = [ (3rd elementary symmetric function of S(n))/(first elementary symmetric function of S(n)) ], where S(n) = {first n+2 positive integers congruent to 1 mod 3}.

Source: https://oeis.org/A024220
Credit: @vivanpoddar

The sequence (offset 1) begins 2, 19, 71, 188, 410, 784, 1367, 2226, 3435, 5078, ...
It is defined as in the name of the entry: S(n) is the multiset of the first n+2 positive integers
congruent to 1 mod 3, that is 1, 4, 7, ..., and a(n) is the floor of the quotient of its
3rd elementary symmetric function by its first one (Mathlib's Multiset.esymm, natural number
division).

Conjecture (R. J. Mathar, Oct 08 2011): a(n) = 4*a(n-1) - 6*a(n-2) + 5*a(n-3) - 5*a(n-4) + 6*a(n-5) - 4*a(n-6) + a(n-7).
G.f.: x*(-2-11*x-7*x^2-8*x^3+x^4) / ( (1+x+x^2)*(x-1)^5 ).
The recurrence involves a(n-7) and the offset is 1, so it is stated for n >= 8. The generating
function is the series Sum_(n>=1) a(n) x^n, and the claim is stated as the identity
G(x) * denominator = numerator between formal power series over the integers.
-/

namespace OMA.S_oeis_a024220

open PowerSeries

/-- S(n): the first n+2 positive integers congruent to 1 mod 3. -/
def S (n : ℕ) : Multiset ℕ := (Multiset.range (n + 2)).map (fun i => 3 * i + 1)

/-- A024220: floor of the quotient of the 3rd by the first elementary symmetric function of S(n). -/
def a (n : ℕ) : ℕ := (S n).esymm 3 / (S n).esymm 1

/-- The conjectured recurrence and generating function for A024220. -/
theorem main :
    (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 5 * a (n - 3) - 5 * a (n - 4) + 6 * a (n - 5) - 4 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * ((1 + X + X ^ 2) * (X - 1) ^ 5)
      = X * (-2 - 11 * X - 7 * X ^ 2 - 8 * X ^ 3 + X ^ 4) := by
  sorry

end OMA.S_oeis_a024220
