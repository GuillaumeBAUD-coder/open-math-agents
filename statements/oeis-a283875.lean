import Mathlib

/-!
# OEIS A283875: every number > 7 is a sum of at most 4 twin primes

Source: https://oeis.org/A283875 (OEIS Foundation, CC BY-SA 4.0).

Entry: Number of partitions of n into twin primes (A001097).

Conjecture (Ilya Gutkovskiy, Mar 17 2017): every number > 7 is the sum of at
most 4 twin primes. For example: 8 = 5 + 3; 9 = 3 + 3 + 3; 10 = 5 + 5;
11 = 5 + 3 + 3; 12 = 7 + 5.

Formalization notes:
* A001097 (twin primes) consists of the primes p such that p - 2 or p + 2 is
  also prime: 3, 5, 7, 11, 13, 17, 19, 29, ... (`IsTwinPrime`; for p = 2,
  `p - 2 = 0` in ℕ is not prime, so 2 is correctly excluded).
* As in the partitions counted by the entry, a twin prime may be used more than
  once (9 = 3 + 3 + 3), so the summands form a list with repetitions allowed.
  "At most 4" is a list of length at most 4; its sum is n > 7, so it is nonempty.
-/

namespace OMA.S_oeis_a283875

/-- p is a twin prime (A001097): p is prime and p - 2 or p + 2 is prime. -/
def IsTwinPrime (p : ℕ) : Prop := p.Prime ∧ ((p - 2).Prime ∨ (p + 2).Prime)

/-- Every number greater than 7 is the sum of at most 4 twin primes. -/
theorem main :
    ∀ n : ℕ, 7 < n →
      ∃ l : List ℕ, l.length ≤ 4 ∧ (∀ p ∈ l, IsTwinPrime p) ∧ l.sum = n := by
  sorry

end OMA.S_oeis_a283875
