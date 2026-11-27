import Mathlib

/-!
# A191993: a(n) = 3^(n-1) + C(2*n, n)/2.

Source: https://oeis.org/A191993
Credit: @agchua

R. J. Mathar (Oct 18 2017), in the formula section of A191993:
  Conjecture: n*(n-3)*a(n) - (7*n^2 -23*n +12)*a(n-1) +6*(2*n-3)*(n-2)*a(n-2)=0.
The sequence has offset 1 (a(1) = 2). The recurrence uses a(n-2), so the conjecture is stated
for n ≥ 3 (then n, n-1, n-2 are all indices of the sequence). The definition is computed in ℚ,
so that C(2n, n)/2 is an exact division (C(2n, n) is even for n ≥ 1, so the values are integers).
-/

namespace OMA.S_oeis_a191993

/-- A191993(n) = 3^(n-1) + C(2n, n)/2 for n ≥ 1. -/
def a (n : ℕ) : ℚ := (3 : ℚ) ^ (n - 1) + ((2 * n).choose n : ℚ) / 2

/-- Mathar's conjecture: for n ≥ 3, n(n-3) a(n) - (7n^2-23n+12) a(n-1) + 6(2n-3)(n-2) a(n-2) = 0. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℚ) * ((n : ℚ) - 3) * a n - (7 * (n : ℚ) ^ 2 - 23 * (n : ℚ) + 12) * a (n - 1)
      + 6 * (2 * (n : ℚ) - 3) * ((n : ℚ) - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a191993
