import Mathlib

/-!
# A052227: a(n) = (4*n+1)*binomial(3*n,n)/(2*n+1).

Source: https://oeis.org/A052227
Credit: @marcelopierry

Conjecture (R. J. Mathar, Nov 24 2012, in the formulas of A052227):
8*n*(2*n+1)*a(n) + 6*(-8*n^2-25*n+13)*a(n-1) - 45*(3*n-4)*(3*n-5)*a(n-2) = 0.

Conventions:
* The sequence has offset 0 (data 1, 5, 27, 156, 935, 5733, ...); the quotient is computed in
  the rationals (the values are integers).
* The recurrence involves a(n-2), so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a052227

/-- A052227(n) = (4n+1)*binomial(3n,n)/(2n+1). -/
def a (n : ℕ) : ℚ := (4 * n + 1) * ((3 * n).choose n : ℚ) / (2 * n + 1)

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    8 * (n : ℚ) * (2 * n + 1) * a n + 6 * (-8 * (n : ℚ) ^ 2 - 25 * n + 13) * a (n - 1) -
      45 * (3 * (n : ℚ) - 4) * (3 * n - 5) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a052227
