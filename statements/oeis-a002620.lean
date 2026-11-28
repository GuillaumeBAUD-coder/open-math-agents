import Mathlib

/-!
# A002620: Oppermann's conjecture in terms of the quarter-squares

Source: https://oeis.org/A002620
Credit: @jagraj28

A002620 is the sequence of quarter-squares `a(n) = floor(n/2) * ceiling(n/2) = floor(n^2/4)`.
The entry records (Ivan N. Ianakiev, 2013) an alternative statement of Oppermann's conjecture:
for `n > 2`, there is at least one prime between `a(n)` and `a(n+1)`.

`main` states it with `a(n) = n^2 / 4` (natural-number division, which is the floor), and
reads between as strictly between: `a(n) < p < a(n+1)`. For `n = 2k` this interval is
`(k^2, k^2 + k)` and for `n = 2k + 1` it is `(k^2 + k, (k + 1)^2)`, the two halves of
Oppermann's conjecture, which is why the source calls it an alternative statement.
-/

namespace OMA.S_oeis_a002620

/-- The quarter-squares, OEIS A002620: `a(n) = floor(n^2 / 4)`. -/
def a (n : ℕ) : ℕ := n ^ 2 / 4

/-- For `n > 2` there is a prime strictly between `a(n)` and `a(n+1)`. -/
theorem main : ∀ n : ℕ, 2 < n → ∃ p : ℕ, p.Prime ∧ a n < p ∧ p < a (n + 1) := by
  sorry

end OMA.S_oeis_a002620
