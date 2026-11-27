import Mathlib

/-!
Do any odd weird numbers exist?

Source: https://en.wikipedia.org/wiki/Weird_number
Credit: @Tchikrazi
-/

namespace OMA.S_wp_do_any_odd_weird_numbers_exist

/-- A weird number is abundant and no subset of its proper divisors sums to it. -/
def IsWeird (n : ℕ) : Prop :=
  n < ∑ d ∈ n.properDivisors, d ∧
    ¬ ∃ s : Finset ℕ, s ⊆ n.properDivisors ∧ (∑ d ∈ s, d) = n

theorem main : ∃ n : ℕ, Odd n ∧ IsWeird n := by
  sorry

end OMA.S_wp_do_any_odd_weird_numbers_exist
