import Mathlib

/-!
Are there infinitely many safe and Sophie Germain primes?

Source: https://en.wikipedia.org/wiki/Safe_and_Sophie_Germain_primes
Credit: @Tchikrazi
-/

namespace OMA.S_wp_are_there_infinitely_many_safe_and_sophie_germain_primes

/-- A Sophie Germain prime p has 2p + 1 prime, called a safe prime. -/
def IsSophieGermainPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (2 * p + 1)

theorem main : {p : ℕ | IsSophieGermainPrime p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_safe_and_sophie_germain_primes
