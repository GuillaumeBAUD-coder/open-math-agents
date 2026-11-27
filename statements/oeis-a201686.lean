import Mathlib

/-!
# A201686: a(n) = binomial(n, [n/2]) - 2.

Source: https://oeis.org/A201686
Credit: @marcelopierry

Conjecture (R. J. Mathar, Jul 17 2014, in the formulas of A201686):
(n+1)*a(n) + 2*(-n-1)*a(n-1) + (-3*n+7)*a(n-2) + 2*(4*n-9)*a(n-3) + 4*(-n+3)*a(n-4) = 0.

Conventions:
* The sequence has offset 0 ([n/2] is the floor, natural-number division), computed in the
  integers (data -1, -1, 0, 1, 4, 8, 18, ...).
* The recurrence involves a(n-4), so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a201686

/-- A201686(n) = binomial(n, floor(n/2)) - 2. -/
def a (n : ℕ) : ℤ := (n.choose (n / 2) : ℤ) - 2

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 1) * a n + 2 * (-(n : ℤ) - 1) * a (n - 1) + (-3 * (n : ℤ) + 7) * a (n - 2) +
      2 * (4 * (n : ℤ) - 9) * a (n - 3) + 4 * (-(n : ℤ) + 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a201686
