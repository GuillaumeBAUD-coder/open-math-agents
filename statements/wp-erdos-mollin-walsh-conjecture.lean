import Mathlib

/-!
Erdős–Mollin–Walsh conjecture.

Source: https://en.wikipedia.org/wiki/Powerful_number#Mathematical_properties
Credit: @Tchikrazi
-/

namespace OMA.S_wp_erdos_mollin_walsh_conjecture

/-- A positive integer is powerful when the square of every prime divisor divides it. -/
def IsPowerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

theorem main : ∀ n : ℕ, ¬ (IsPowerful n ∧ IsPowerful (n + 1) ∧ IsPowerful (n + 2)) := by
  sorry

end OMA.S_wp_erdos_mollin_walsh_conjecture
