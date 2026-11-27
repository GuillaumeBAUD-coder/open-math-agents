import Mathlib

/-!
# Are there infinitely many Giuga numbers?

Source: https://en.wikipedia.org/wiki/Giuga_number
Credit: @mrjellyfish5
-/

namespace OMA.S_wp_are_there_infinitely_many_giuga_numbers

/-- A composite natural number whose prime divisors each divide the quotient minus one. -/
def IsGiugaNumber (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∣ (n / p - 1)

theorem main : Set.Infinite {n : ℕ | IsGiugaNumber n} := by
  sorry

end OMA.S_wp_are_there_infinitely_many_giuga_numbers
