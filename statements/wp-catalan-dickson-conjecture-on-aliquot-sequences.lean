import Mathlib

/-!
The Catalan–Dickson conjecture on aliquot sequences.

Source: https://en.wikipedia.org/wiki/Aliquot_sequence#Catalan-Dickson_conjecture
Credit: @Tchikrazi
-/

namespace OMA.S_wp_catalan_dickson_conjecture_on_aliquot_sequences

/-- Iterate the sum of proper divisors, with 0 remaining 0. -/
def aliquotSequence (start : ℕ) : ℕ → ℕ
  | 0 => start
  | n + 1 => ∑ d ∈ (aliquotSequence start n).properDivisors, d

/-- Every aliquot sequence terminates at 0 or eventually repeats. -/
theorem main :
    ∀ start : ℕ, 0 < start →
      ∃ i j : ℕ, i < j ∧ aliquotSequence start i = aliquotSequence start j := by
  sorry

end OMA.S_wp_catalan_dickson_conjecture_on_aliquot_sequences
