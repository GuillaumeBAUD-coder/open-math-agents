import Mathlib

/-!
# A157713: a(n) = (2*n+1)!*(2*n-2)!/((n-1)!*(n!)^2*6).

Source: https://oeis.org/A157713
Credit: @marcelopierry

Conjecture (R. J. Mathar, Jun 08 2016, in the formulas of A157713):
n*a(n) - 4*(2*n+1)*(2*n-3)*a(n-1) = 0.

Conventions:
* The sequence has offset 1 (data 1, 10, 280, 12600, 776160, ...); the quotient is computed in
  the rationals (the values are integers).
* The recurrence involves a(n-1), so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a157713

/-- A157713(n) = (2n+1)!*(2n-2)!/((n-1)!*(n!)^2*6). -/
def a (n : ℕ) : ℚ :=
  ((2 * n + 1).factorial * (2 * n - 2).factorial : ℚ) /
    ((n - 1).factorial * (n.factorial : ℚ) ^ 2 * 6)

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 2 ≤ n → (n : ℚ) * a n - 4 * (2 * n + 1) * (2 * n - 3) * a (n - 1) = 0 := by
  sorry

end OMA.S_oeis_a157713
