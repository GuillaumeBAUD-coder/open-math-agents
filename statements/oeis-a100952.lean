import Mathlib

/-!
# A100952: Numbers that cannot be written as p*q+r with three distinct primes p, q and r.

Source: https://oeis.org/A100952
Credit: @keiichisince1986-bot

A100952 lists the positive integers that cannot be written as `p * q + r` with `p, q, r` three
distinct primes:
`1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 24, 30, 36, 42, 60`.
The entry states: Conjecture: the sequence is complete.

Conventions:
- The terms are positive integers, as in the data (`0` cannot be written in this form either,
  but it is not considered).
- `p, q, r` are pairwise distinct primes.
- Complete means that the data list every term, so the conjecture says that the set of positive
  integers that cannot be written in this form is exactly the set of the 21 numbers above.
-/

namespace OMA.S_oeis_a100952

theorem main :
    {n : ℕ | 0 < n ∧ ¬ ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
        n = p * q + r} =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 24, 30, 36, 42, 60} := by
  sorry

end OMA.S_oeis_a100952
