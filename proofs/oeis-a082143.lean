import OMAStatements.S_oeis_a082143
import Mathlib

-- Problem: oeis-a082143
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P082143
open OMA.S_oeis_a082143

lemma ratio (m : ℕ) : ((2 * m + 3).choose (m + 1) : ℚ) * ((m : ℚ) + 2) = ((2 * m + 1).choose m : ℚ) * (2 * (2 * (m : ℚ) + 3)) := by
  rw [Nat.cast_choose ℚ (by omega), Nat.cast_choose ℚ (by omega),
    show 2 * m + 3 - (m + 1) = (m + 1) + 1 by omega, show 2 * m + 1 - m = m + 1 by omega,
    show 2 * m + 3 = (2 * m + 1 + 1) + 1 by ring, Nat.factorial_succ (2 * m + 1 + 1),
    Nat.factorial_succ (2 * m + 1), Nat.factorial_succ (m + 1), Nat.factorial_succ m]
  have h1 : (m.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((m + 1).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem sol : type_of% @OMA.S_oeis_a082143.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold a T
  rw [show m + 2 - 1 = m + 1 by omega]
  have z1 : (0 : ℚ) ^ (m + 2) = 0 := by simp
  have z2 : (0 : ℚ) ^ (m + 1) = 0 := by simp
  have p1 : (2 : ℚ) ^ (((m + 2 : ℕ) : ℤ) - 1) = 2 ^ (m + 1) := by
    rw [show ((m + 2 : ℕ) : ℤ) - 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have p2 : (2 : ℚ) ^ (((m + 1 : ℕ) : ℤ) - 1) = 2 ^ m := by
    rw [show ((m + 1 : ℕ) : ℤ) - 1 = ((m : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [z1, z2, p1, p2, show m + 2 + (m + 2 + 1) = 2 * (m + 1) + 3 by ring,
    show m + 1 + (m + 1 + 1) = 2 * m + 3 by ring]
  have r1 := ratio (m + 1)
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, show m + 1 + 1 = m + 2 by ring] at r1
  push_cast at r1 ⊢
  linear_combination (2 : ℚ) ^ (m + 1) * r1

end OMA.P082143

theorem OMA.solution : type_of% @OMA.S_oeis_a082143.main := OMA.P082143.sol
