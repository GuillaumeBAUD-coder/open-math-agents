import Mathlib

/-!
# Are there infinitely many Woodall primes?

Source: https://en.wikipedia.org/wiki/Woodall_number#Woodall_primes
Credit: @Andyi955

A Woodall number is a natural number of the form `W n = n * 2 ^ n - 1`, and a Woodall prime is a
Woodall number that is prime. The first few exponents `n` for which `W n` is prime are
`2, 3, 6, 30, 75, 81, 115, 123, 249, 362, 384, ...` (OEIS A002234); it is an open problem whether
there are infinitely many Woodall primes (Wikipedia, Woodall number, section Woodall primes).

## Encoding

* A Woodall number is indexed by its exponent `n`, and the question of infinitely many Woodall
  primes is the question that the set of exponents `k` with `k * 2 ^ k - 1` prime is infinite:
  `W` is strictly increasing in `k`, so the set of Woodall primes is infinite exactly when the set
  of such exponents is.
* The index is restricted to `1 < k`, matching the reference statement for this problem in the
  formal-conjectures catalogue (`FormalConjectures/Wikipedia/WoodalPrimes.lean`) and the OEIS list
  of exponents, which starts at `2`. This restriction changes nothing: `W 0 = 0` and `W 1 = 1` are
  not prime, so no Woodall prime is lost.
* `Nat.Prime` is Mathlib's prime predicate; `Set.Infinite` is infinitude of the set of exponents.
-/

namespace OMA.S_wp_are_there_infinitely_many_woodall_primes

/-- **Infinitely many Woodall primes**: infinitely many `k > 1` have `k * 2 ^ k - 1` prime. -/
theorem main : {k : ℕ | 1 < k ∧ (k * 2 ^ k - 1).Prime}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_woodall_primes
