import Mathlib

/-!
# A247838: numbers k with sigma(sigma(k)) prime (products of distinct Mersenne primes)

Source: https://oeis.org/A247838 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A247838 (offset 1): numbers k such that sigma(sigma(k)) is prime; data
3, 2667, 3937, 57337, 172011, 253921, ... (sigma(sigma(2667)) = sigma(4096) = 8191).

The entry records two conjectures:

  Conjecture: Subsequence of A046528 (numbers that are a product of distinct Mersenne primes).
  Corresponding values of primes p: 7, 8191, 8191, 131071, 524287, 524287, ... (A247822).
  Conjecture: values of primes p is equal to Mersenne primes (A000668).

Both are stated here, as a conjunction.

Reading of the source:
* `sigma` is the sum of divisors (`ArithmeticFunction.sigma 1`); `k` ranges over the positive
  integers.
* A Mersenne prime is a prime of the form `2^q - 1`. A product of distinct Mersenne primes is
  `∏ S` for a finite set `S` of Mersenne primes (A046528 starts with the empty product 1).
* The second conjecture says that the prime `sigma(sigma(k))` is a Mersenne prime (the listed
  values are all Mersenne primes; "is equal to" is read as membership, since values repeat).
-/

namespace OMA.S_oeis_a247838

open ArithmeticFunction

/-- `p` is a Mersenne prime: a prime of the form `2^q - 1`. -/
def IsMersennePrime (p : ℕ) : Prop := p.Prime ∧ ∃ q : ℕ, p = 2 ^ q - 1

/-- If `σ(σ(k))` is prime, then `k` is a product of distinct Mersenne primes and `σ(σ(k))` is a
Mersenne prime. -/
theorem main : ∀ k : ℕ, 0 < k → (sigma 1 (sigma 1 k)).Prime →
    (∃ S : Finset ℕ, (∀ p ∈ S, IsMersennePrime p) ∧ k = ∏ p ∈ S, p) ∧
      IsMersennePrime (sigma 1 (sigma 1 k)) := by
  sorry

end OMA.S_oeis_a247838
