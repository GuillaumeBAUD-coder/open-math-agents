import Mathlib

/-!
# A152484: Odd numbers which are not the sum of an even semiprime and an odd semiprime.

Source: https://oeis.org/A152484
Credit: @keiichisince1986-bot

A152484 lists the odd numbers that are not the sum of an even semiprime and an odd semiprime:
`1, 3, 5, 7, 9, 11, 17, 33`.
The entry states: No more terms < 10^9. Conjectured to be complete.

Conventions:
- A semiprime is a product of two primes, not necessarily distinct (A001358): a number whose
  prime factorization, counted with multiplicity, has length `2`. The even semiprimes are the
  numbers `2 p` with `p` prime (A100484: 4, 6, 10, 14, …); the odd semiprimes are A046315
  (9, 15, 21, 25, …).
- Complete means that the data list every term, so the conjecture says that the set of odd
  numbers that are not such a sum is exactly `{1, 3, 5, 7, 9, 11, 17, 33}`.
-/

namespace OMA.S_oeis_a152484

/-- `n` is a semiprime: a product of exactly two primes counted with multiplicity. -/
def IsSemiprime (n : ℕ) : Prop :=
  n.primeFactorsList.length = 2

theorem main :
    {n : ℕ | Odd n ∧
        ¬ ∃ a b : ℕ, Even a ∧ IsSemiprime a ∧ Odd b ∧ IsSemiprime b ∧ n = a + b} =
      {1, 3, 5, 7, 9, 11, 17, 33} := by
  sorry

end OMA.S_oeis_a152484
