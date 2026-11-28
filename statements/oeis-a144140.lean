import Mathlib

/-!
# A144140: Numbers n such that between n^K and (n+1)^K there are no primes, where K = 3/2.

Source: https://oeis.org/A144140
Credit: @keiichisince1986-bot

A144140 lists the positive integers `n` such that no prime lies between `n^(3/2)` and
`(n+1)^(3/2)`:
`10, 20, 24, 27, 32, 65, 121, 139, 141, 187, 306, 321, 348, 1006, 1051`.
The entry states: Conjecture: this sequence is finite and complete.

Conventions:
- The powers are real powers `x ^ (3/2 : ℝ)`, and between is strict: there is no prime `p` with
  `n^(3/2) < p < (n+1)^(3/2)`. (When `n` is a perfect square, `n^(3/2)` is an integer; the data
  follow the strict reading.)
- The terms are positive integers, as in the data (`n = 0` would satisfy the condition, as there
  is no prime between `0` and `1`, but it is not considered).
- Finite and complete means that the data list every term, so the conjecture says that the set
  of such positive `n` is exactly the set of the 15 numbers above.
-/

namespace OMA.S_oeis_a144140

theorem main :
    {n : ℕ | 0 < n ∧ ¬ ∃ p : ℕ, p.Prime ∧ (n : ℝ) ^ (3 / 2 : ℝ) < p ∧
        (p : ℝ) < ((n : ℝ) + 1) ^ (3 / 2 : ℝ)} =
      {10, 20, 24, 27, 32, 65, 121, 139, 141, 187, 306, 321, 348, 1006, 1051} := by
  sorry

end OMA.S_oeis_a144140
