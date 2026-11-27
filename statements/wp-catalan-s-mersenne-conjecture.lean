import Mathlib

/-!
Catalan's Mersenne conjecture.

Source: https://en.wikipedia.org/wiki/Catalan%27s_Mersenne_conjecture
Credit: @Tchikrazi
-/

namespace OMA.S_wp_catalan_s_mersenne_conjecture

/-- The Catalan–Mersenne sequence starts at 2 and iterates n ↦ 2ⁿ − 1. -/
def catalanMersenne : ℕ → ℕ
  | 0 => 2
  | n + 1 => 2 ^ catalanMersenne n - 1

/-- Some Catalan–Mersenne number is composite. -/
theorem main : ∃ n : ℕ, 1 < catalanMersenne n ∧ ¬ Nat.Prime (catalanMersenne n) := by
  sorry

end OMA.S_wp_catalan_s_mersenne_conjecture
