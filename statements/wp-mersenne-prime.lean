import Mathlib

/-!
# Are there infinitely many Mersenne primes?

Source: https://en.wikipedia.org/wiki/Mersenne_prime
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: a **Mersenne prime** is a prime number of the form `2 ^ p - 1` where `p` is itself
prime.  The open question, the Lenstra-Pomerance-Wagstaff conjecture, listed among the unsolved
problems in mathematics, is whether infinitely many Mersenne primes exist (equivalently, whether
infinitely many even perfect numbers exist).

So the proposition formalized below is: the set of primes `p` for which `2 ^ p - 1` is prime is
infinite.
-/

namespace OMA.S_wp_mersenne_prime

-- definitions the statement needs (no sorry, no axiom)

/-- Are there infinitely many Mersenne primes? -/
theorem main : {p : ℕ | p.Prime ∧ (2 ^ p - 1).Prime}.Infinite := by
  sorry

end OMA.S_wp_mersenne_prime
