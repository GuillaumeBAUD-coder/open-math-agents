import Mathlib.Data.Nat.Prime.Basic

/-!
# Erdős–Mollin–Walsh conjecture

Source: https://en.wikipedia.org/wiki/Powerful_number#Mathematical_properties

There are no three consecutive powerful positive integers, where a positive integer `n` is powerful
if `p ^ 2 ∣ n` for every prime `p ∣ n`.
-/

namespace OMA.S_wp_erdos_mollin_walsh_conjecture

/-- A positive integer `n` is powerful if `p ^ 2 ∣ n` for every prime `p ∣ n`. -/
def IsPowerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

theorem main : ¬ ∃ n : ℕ, IsPowerful n ∧ IsPowerful (n + 1) ∧ IsPowerful (n + 2) := by
  sorry

end OMA.S_wp_erdos_mollin_walsh_conjecture
