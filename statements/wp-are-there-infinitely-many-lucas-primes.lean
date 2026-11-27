import Mathlib

/-!
# Are there infinitely many Lucas primes?

A Lucas prime is a prime value of the Lucas sequence, including its initial value 2.
See https://en.wikipedia.org/wiki/Lucas_number#Relationships_with_prime_numbers.
-/

namespace OMA.S_wp_are_there_infinitely_many_lucas_primes

/-- The Lucas sequence indexed from zero. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- Infinitely many distinct primes occur in the Lucas sequence. -/
theorem main : Set.Infinite {p : ℕ | p.Prime ∧ p ∈ Set.range lucas} := by
  sorry

end OMA.S_wp_are_there_infinitely_many_lucas_primes
