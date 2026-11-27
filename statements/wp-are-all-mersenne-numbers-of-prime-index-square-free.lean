import Mathlib

/-!
Are all Mersenne numbers of prime index square-free?

Source: https://en.wikipedia.org/wiki/Mersenne_number
Reference: https://msp.org/pjm/1967/22-3/pjm-v22-n3-p15-s.pdf
Credit: @Tchikrazi
-/

namespace OMA.S_wp_are_all_mersenne_numbers_of_prime_index_square_free

theorem main : ∀ p : ℕ, Nat.Prime p → Squarefree (2 ^ p - 1) := by
  sorry

end OMA.S_wp_are_all_mersenne_numbers_of_prime_index_square_free
