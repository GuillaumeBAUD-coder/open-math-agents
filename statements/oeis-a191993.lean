import Mathlib

/-!
# A191993: a(n) = 3^(n-1) + C(2*n, n)/2.

Source: https://oeis.org/A191993
Credit: @rorcores

The entry (offset 1, data 2, 6, 19, 62, 207, 705, 2445, ...) records in its FORMULA section:

  Conjecture: n*(n-3)*a(n) - (7*n^2 -23*n +12)*a(n-1) +6*(2*n-3)*(n-2)*a(n-2)=0.
  - R. J. Mathar, Oct 18 2017

Conventions:
* `a n = 3^(n-1) + C(2n, n)/2` for `n ≥ 1` (the offset of the sequence), exactly the name of the
  sequence. For `n ≥ 1` the central binomial coefficient `C(2n, n)` is even, so the
  natural-number division by 2 is exact; this gives `a 1, ..., a 5` = 2, 6, 19, 62, 207, matching
  the data (the entry's example is `a(5) = 3^4 + C(10,5)/2 = 81 + 126 = 207`).
* The recurrence involves `a(n-2)`, and the sequence starts at index 1, so it is stated for every
  `n ≥ 3` (the source gives no range; these are all the `n` for which the three terms exist).
* The identity is stated in `ℤ`, as written in the source, so that no truncated subtraction occurs.
-/

namespace OMA.S_oeis_a191993

/-- A191993: `a n = 3^(n-1) + C(2n, n)/2` (for `n ≥ 1`). -/
def a (n : ℕ) : ℕ := 3 ^ (n - 1) + (2 * n).choose n / 2

/-- Mathar's conjectured recurrence:
`n(n-3) a(n) - (7n^2-23n+12) a(n-1) + 6(2n-3)(n-2) a(n-2) = 0` for `n ≥ 3`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℤ) * ((n : ℤ) - 3) * (a n : ℤ)
      - (7 * (n : ℤ) ^ 2 - 23 * (n : ℤ) + 12) * (a (n - 1) : ℤ)
      + 6 * (2 * (n : ℤ) - 3) * ((n : ℤ) - 2) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a191993
