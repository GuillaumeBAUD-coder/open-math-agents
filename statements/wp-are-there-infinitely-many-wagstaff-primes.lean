import Mathlib

/-!
Are there infinitely many Wagstaff primes?

Source: https://en.wikipedia.org/wiki/Wagstaff_prime
Credit: @Tchikrazi
-/

namespace OMA.S_wp_are_there_infinitely_many_wagstaff_primes

/-- A Wagstaff prime is (2^q + 1) / 3 for an odd prime q. -/
def IsWagstaffPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ q : ℕ, Nat.Prime q ∧ Odd q ∧ p = (2 ^ q + 1) / 3

theorem main : {p : ℕ | IsWagstaffPrime p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_wagstaff_primes
