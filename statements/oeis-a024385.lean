import Mathlib

/-!
# A024385: a(n) = [ (2nd elementary symmetric function of S(n))/(first elementary symmetric function of S(n)) ], where S(n) = {first n+1 positive integers congruent to 1 mod 4}.

Source: https://oeis.org/A024385
Credit: @vivanpoddar

The sequence (offset 1) begins 0, 3, 9, 16, 25, 36, 49, 64, 82, 101, ...
It is defined as in the name of the entry: S(n) is the multiset of the first n+1 positive integers
congruent to 1 mod 4, that is 1, 5, 9, ..., and a(n) is the floor of the quotient of its
2nd elementary symmetric function by its first one (Mathlib's Multiset.esymm, natural number
division).

Conjecture (R. J. Mathar, Oct 08 2011): a(n) = 2*a(n-1) - a(n-2) + a(n-6) - 2*a(n-7) + a(n-8).
G.f.: x^2*(-3-3*x-x^2-2*x^3-2*x^4-2*x^5+x^6) / ( (1+x)*(1+x+x^2)*(x^2-x+1)*(x-1)^3 ).
The recurrence involves a(n-8) and the offset is 1, so it is stated for n >= 9. The generating
function is the series Sum_(n>=1) a(n) x^n, and the claim is stated as the identity
G(x) * denominator = numerator between formal power series over the integers.
-/

namespace OMA.S_oeis_a024385

open PowerSeries

/-- S(n): the first n+1 positive integers congruent to 1 mod 4. -/
def S (n : ℕ) : Multiset ℕ := (Multiset.range (n + 1)).map (fun i => 4 * i + 1)

/-- A024385: floor of the quotient of the 2nd by the first elementary symmetric function of S(n). -/
def a (n : ℕ) : ℕ := (S n).esymm 2 / (S n).esymm 1

/-- The conjectured recurrence and generating function for A024385. -/
theorem main :
    (∀ n : ℕ, 9 ≤ n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2) + a (n - 6) - 2 * a (n - 7) + a (n - 8)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * ((1 + X) * (1 + X + X ^ 2) * (X ^ 2 - X + 1) * (X - 1) ^ 3)
      = X ^ 2 * (-3 - 3 * X - X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 - 2 * X ^ 5 + X ^ 6) := by
  sorry

end OMA.S_oeis_a024385
