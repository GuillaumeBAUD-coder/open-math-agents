import Mathlib

/-!
Are there infinitely many Mersenne primes?

Source: https://en.wikipedia.org/wiki/Mersenne_prime
Credit: @Tchikrazi
-/

namespace OMA.S_wp_mersenne_prime

/-- A Mersenne prime is a prime of the form 2ⁿ − 1. -/
def IsMersennePrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ n : ℕ, p = 2 ^ n - 1

theorem main : {p : ℕ | IsMersennePrime p}.Infinite := by
  sorry

end OMA.S_wp_mersenne_prime
