import Mathlib

/-!
Are there infinitely many Lucas primes?

Source: https://en.wikipedia.org/wiki/Lucas_number#Lucas_primes
Credit: @Tchikrazi
-/

namespace OMA.S_wp_are_there_infinitely_many_lucas_primes

/-- The Lucas sequence starts with 2 and 1 and uses the Fibonacci recurrence. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

def IsLucasPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ n : ℕ, p = lucas n

theorem main : {p : ℕ | IsLucasPrime p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_lucas_primes
