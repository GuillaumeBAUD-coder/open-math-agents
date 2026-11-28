import Mathlib

/-!
# A152483: Even numbers which are not the sum of 2 odd semiprimes.

Source: https://oeis.org/A152483
Credit: @keiichisince1986-bot

A152483 lists the even numbers that are not the sum of two odd semiprimes:
`2, 4, 6, 8, 10, 12, 14, 16, 20, 22, 26, 28, 32, 38, 52, 62`.
The entry states: No more terms < 10^9. Conjectured to be complete.

Conventions:
- A semiprime is a product of two primes, not necessarily distinct (A001358): a number whose
  prime factorization, counted with multiplicity, has length `2`. `IsOddSemiprime n` adds that
  `n` is odd (A046315: 9, 15, 21, 25, 33, …).
- A sum of two odd semiprimes is `a + b` with `a` and `b` odd semiprimes; `a = b` is allowed
  (`18 = 9 + 9` is not a term).
- The even numbers here are the positive even numbers, as in the data (which start at `2`).
- Complete means that the data list every term, so the conjecture says that the set of positive
  even numbers that are not such a sum is exactly the set of the 16 numbers above.
-/

namespace OMA.S_oeis_a152483

/-- `n` is an odd semiprime: odd, and a product of exactly two primes counted with multiplicity. -/
def IsOddSemiprime (n : ℕ) : Prop :=
  Odd n ∧ n.primeFactorsList.length = 2

theorem main :
    {n : ℕ | 0 < n ∧ Even n ∧ ¬ ∃ a b : ℕ, IsOddSemiprime a ∧ IsOddSemiprime b ∧ n = a + b} =
      {2, 4, 6, 8, 10, 12, 14, 16, 20, 22, 26, 28, 32, 38, 52, 62} := by
  sorry

end OMA.S_oeis_a152483
