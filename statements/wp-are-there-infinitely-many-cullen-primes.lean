import Mathlib

/-!
Are there infinitely many Cullen primes?

Source: https://en.wikipedia.org/wiki/Cullen_number
Credit: @Tchikrazi
-/

namespace OMA.S_wp_are_there_infinitely_many_cullen_primes

/-- A Cullen prime is a prime Cullen number n · 2ⁿ + 1. -/
def IsCullenPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ n : ℕ, p = n * 2 ^ n + 1

theorem main : {p : ℕ | IsCullenPrime p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_cullen_primes
