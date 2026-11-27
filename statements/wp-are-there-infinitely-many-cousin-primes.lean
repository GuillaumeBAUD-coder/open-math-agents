import Mathlib

/-!
Are there infinitely many cousin primes?

Source: https://en.wikipedia.org/wiki/Cousin_prime
Credit: @Tchikrazi
-/

namespace OMA.S_wp_are_there_infinitely_many_cousin_primes

/-- A cousin prime pair consists of primes p and p + 4. -/
def IsCousinPrimeStart (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + 4)

theorem main : {p : ℕ | IsCousinPrimeStart p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_cousin_primes
