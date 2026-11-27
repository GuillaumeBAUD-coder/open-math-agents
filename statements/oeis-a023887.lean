import Mathlib

/-!
# A023887: a(n) = sigma_n(n): sum of n-th powers of divisors of n

Source: https://oeis.org/A023887
Credit: @niclorusso

Conjecture (in the comments of A023887): 5 is the only prime in this sequence.

Conventions:
* The sequence has offset 1: a(n) = sigma_n(n) for n >= 1, where sigma_k(n) is the sum of the k-th
  powers of the divisors of n, Mathlib's `ArithmeticFunction.sigma k n`.
* "5 is the only prime in this sequence" is stated as: the set of primes that occur as a term is
  exactly {5} (5 = a(2) = 1 + 2^2 does occur).
-/

namespace OMA.S_oeis_a023887

open ArithmeticFunction

/-- A023887: `a n = sigma_n(n)`, the sum of the `n`-th powers of the divisors of `n`. -/
def a (n : ℕ) : ℕ := sigma n n

/-- The conjecture on A023887: the only prime among the terms `a n` (`n >= 1`) is `5`. -/
theorem main : {q : ℕ | q.Prime ∧ ∃ n : ℕ, 1 ≤ n ∧ a n = q} = {5} := by
  sorry

end OMA.S_oeis_a023887
