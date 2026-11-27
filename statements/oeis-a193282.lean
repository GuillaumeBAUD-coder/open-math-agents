import Mathlib

/-!
# A193282: a(n) = (n!/floor(n/2)!)^2.

Source: https://oeis.org/A193282
Credit: @agchua

R. J. Mathar (Oct 03 2014), in the formula section of A193282:
  Conjecture: a(n) + 8*a(n-1) - 4*(n-2)*(n+2)*a(n-2) + 16*(-2*n^2 + 6*n - 3)*a(n-3)
  - 64*(n-3)^2*a(n-4) = 0.
The sequence has offset 0 (a(0) = 1). The recurrence uses a(n-4), so the conjecture is stated
for n ≥ 4. floor(n/2) is the natural-number division n / 2, and n!/floor(n/2)! is computed in ℚ
(it is an integer, since floor(n/2)! divides n!).
-/

namespace OMA.S_oeis_a193282

/-- A193282(n) = (n!/floor(n/2)!)^2. -/
def a (n : ℕ) : ℚ := ((n.factorial : ℚ) / ((n / 2).factorial : ℚ)) ^ 2

/-- Mathar's conjecture: the order-4 recurrence holds for all n ≥ 4. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    a n + 8 * a (n - 1) - 4 * ((n : ℚ) - 2) * ((n : ℚ) + 2) * a (n - 2)
      + 16 * (-2 * (n : ℚ) ^ 2 + 6 * (n : ℚ) - 3) * a (n - 3)
      - 64 * ((n : ℚ) - 3) ^ 2 * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a193282
