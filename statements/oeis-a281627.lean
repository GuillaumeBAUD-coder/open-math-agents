import Mathlib

/-!
# A281627: primes of the form sigma(phi(k)) are exactly the Mersenne primes

Source: https://oeis.org/A281627
Credit: @LordMike

"Conjecture 1: If A062402(n) = A000203(A000010(n)) = sigma(phi(n)) is a prime p for some n, then p is Mersenne
prime (A000668); a(n) > 0 for all n."
(a(n) is the smallest k with sigma(phi(k)) the n-th Mersenne prime, or 0 if no such k exists; offset 1.)

Reading used here: the first part says every prime value of sigma(phi(k)) is a Mersenne prime (a prime 2^m - 1);
`a(n) > 0` says every Mersenne prime is attained as sigma(phi(k)) for some k. Together: the two sets of primes
are equal. (k = 0 gives sigma(phi 0) = 0, not prime, so no junk case.) The implicit infinitude of Mersenne primes
is not added.
-/

namespace OMA.S_oeis_a281627

theorem main :
    {q : ℕ | q.Prime ∧ ∃ k, ArithmeticFunction.sigma 1 (Nat.totient k) = q} =
      {q : ℕ | q.Prime ∧ ∃ m, q = 2 ^ m - 1} := by
  sorry

end OMA.S_oeis_a281627
