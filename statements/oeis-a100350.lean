import Mathlib

/-!
# A100350: Primes p such that p-2^k is a prime or semiprime for all k > 0 with 2^k < p.

Source: https://oeis.org/A100350
Credit: @keiichisince1986-bot

A100350 lists the primes `p` such that `p - 2^k` is a prime or a semiprime for every `k > 0` with
`2^k < p`: `7, 11, 13, 19, 23, 37, 41, 73`.
The entry states: No others < 10^9; conjecture that this sequence is finite.

Conventions:
- A number is a prime or a semiprime when its prime factorization, counted with multiplicity,
  has length `1` or `2`.
- For `p = 2` there is no `k > 0` with `2^k < p`, so the condition would hold vacuously; the data
  do not contain `2` (and `3`, `5` fail since `3 - 2 = 5 - 4 = 1`), so the sequence only considers
  `p > 2`. This changes the set by at most one element, so it does not affect finiteness.
- The conjecture says that the set of such primes is finite.
-/

namespace OMA.S_oeis_a100350

theorem main :
    {p : ℕ | p.Prime ∧ 2 < p ∧ ∀ k : ℕ, 0 < k → 2 ^ k < p →
        ((p - 2 ^ k).primeFactorsList.length = 1 ∨
          (p - 2 ^ k).primeFactorsList.length = 2)}.Finite := by
  sorry

end OMA.S_oeis_a100350
