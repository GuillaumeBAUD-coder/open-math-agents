import OMAReductions.R_oeis_a027697_R1_H3_R1
import Mathlib

/-! At most `B` of the integers `x, …, x + B - 1` satisfy any predicate: `Nat.count_add`. -/

theorem OMA.solution : OMA.R_oeis_a027697_R1_H3_R1.H2 := by
  intro x B
  rw [Nat.count_add]
  exact Nat.add_le_add_left (Nat.count_le _) _
