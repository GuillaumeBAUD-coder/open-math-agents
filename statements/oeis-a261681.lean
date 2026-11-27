import Mathlib

/-!
# A261681: a(n) = 2^n + binomial(n, floor(n/2)) - 1.

Source: https://oeis.org/A261681
Credit: @marcelopierry

Conjecture (R. J. Mathar, Jan 04 2017, in the formulas of A261681):
-(n+1)*(n-4)*a(n) + (3*n^2-9*n-8)*a(n-1) + 2*(n^2-9*n+16)*a(n-2) + 4*(-3*n^2+18*n-25)*a(n-3)
+ 8*(n-3)^2*a(n-4) = 0.

Conventions:
* The sequence has offset 0 (floor(n/2) is natural-number division), computed in the integers
  (data 1, 2, 5, 10, 21, 41, 83, ...).
* The recurrence involves a(n-4), so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a261681

/-- A261681(n) = 2^n + binomial(n, floor(n/2)) - 1. -/
def a (n : ℕ) : ℤ := 2 ^ n + (n.choose (n / 2) : ℤ) - 1

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    -((n : ℤ) + 1) * ((n : ℤ) - 4) * a n + (3 * (n : ℤ) ^ 2 - 9 * n - 8) * a (n - 1) +
      2 * ((n : ℤ) ^ 2 - 9 * n + 16) * a (n - 2) + 4 * (-3 * (n : ℤ) ^ 2 + 18 * n - 25) * a (n - 3) +
      8 * ((n : ℤ) - 3) ^ 2 * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a261681
