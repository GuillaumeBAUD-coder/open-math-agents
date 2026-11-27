import Mathlib

/-!
Are there infinitely many sexy primes?

Source: https://en.wikipedia.org/wiki/Sexy_primes
Credit: @Tchikrazi
-/

namespace OMA.S_wp_are_there_infinitely_many_sexy_primes

/-- A sexy prime pair consists of primes p and p + 6. -/
def IsSexyPrimeStart (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + 6)

theorem main : {p : ℕ | IsSexyPrimeStart p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_sexy_primes
