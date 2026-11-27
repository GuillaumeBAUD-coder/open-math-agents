import Mathlib

/-!
The new Mersenne conjecture.

Source: https://en.wikipedia.org/wiki/Mersenne_conjectures#New_Mersenne_conjecture
Credit: @Tchikrazi
-/

namespace OMA.S_wp_new_mersenne_conjecture

/-- The exponent has one of the four forms 2ᵏ ± 1 or 4ᵏ ± 3. -/
def HasExponentForm (p : ℕ) : Prop :=
  ∃ k : ℕ, p + 1 = 2 ^ k ∨ p = 2 ^ k + 1 ∨ p + 3 = 4 ^ k ∨ p = 4 ^ k + 3

/-- For odd p, any two of the three stated conditions imply the third. -/
theorem main :
    ∀ p : ℕ, Odd p →
      let A := HasExponentForm p
      let B := Nat.Prime (2 ^ p - 1)
      let C := Nat.Prime ((2 ^ p + 1) / 3)
      (A → B → C) ∧ (A → C → B) ∧ (B → C → A) := by
  sorry

end OMA.S_wp_new_mersenne_conjecture
