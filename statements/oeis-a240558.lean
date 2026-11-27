import Mathlib

/-!
# A240558: a(n) = 2^n*n!/((floor(n/2)+1)*floor(n/2)!^2).

Source: https://oeis.org/A240558
Credit: @marcelopierry

Conjecture (R. J. Mathar, Jun 14 2016, in the formulas of A240558):
-(n+2)*(n^2-5)*a(n) + 8*(-2*n-1)*a(n-1) + 16*(n-1)*(n^2+2*n-4)*a(n-2) = 0.

Conventions:
* The sequence has offset 0 (floor(n/2) is natural-number division), computed in the
  rationals (data 1, 2, 4, 24, 32, 320, 320, 4480, ...).
* The recurrence involves a(n-2), so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a240558

/-- A240558(n) = 2^n*n!/((floor(n/2)+1)*floor(n/2)!^2). -/
def a (n : ℕ) : ℚ := (2 ^ n * n.factorial : ℚ) / (((n / 2 + 1 : ℕ) : ℚ) * ((n / 2).factorial : ℚ) ^ 2)

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    -((n : ℚ) + 2) * ((n : ℚ) ^ 2 - 5) * a n + 8 * (-2 * (n : ℚ) - 1) * a (n - 1) +
      16 * ((n : ℚ) - 1) * ((n : ℚ) ^ 2 + 2 * n - 4) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a240558
