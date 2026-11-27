import Mathlib

/-!
Are there infinitely many Woodall primes?

Source: https://en.wikipedia.org/wiki/Woodall_number#Woodall_primes
Credit: @Tchikrazi
-/

namespace OMA.S_wp_are_there_infinitely_many_woodall_primes

/-- A Woodall prime is a prime of the form n · 2ⁿ − 1. -/
def IsWoodallPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ n : ℕ, 0 < n ∧ p = n * 2 ^ n - 1

theorem main : {p : ℕ | IsWoodallPrime p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_woodall_primes
