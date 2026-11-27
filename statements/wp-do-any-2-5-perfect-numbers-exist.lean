import Mathlib

/-!
Do any (2, 5)-perfect numbers exist?

Source: https://en.wikipedia.org/wiki/Superperfect_number#Generalizations
Credit: @Tchikrazi
-/

namespace OMA.S_wp_do_any_2_5_perfect_numbers_exist

/-- The sum of positive divisors. -/
def divisorSum (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

theorem main : ∃ n : ℕ, 0 < n ∧ divisorSum (divisorSum n) = 5 * n := by
  sorry

end OMA.S_wp_do_any_2_5_perfect_numbers_exist
