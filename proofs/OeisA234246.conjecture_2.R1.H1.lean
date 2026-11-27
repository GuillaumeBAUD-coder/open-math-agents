import OMAReductions.R_OeisA234246_conjecture_2_R1

/-! Proof of step H1 of OeisA234246.conjecture_2.R1 -/

-- Credit: @nijv

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
theorem OMA.solution : OMA.R_OeisA234246_conjecture_2_R1.H1 := by
  unfold OMA.R_OeisA234246_conjecture_2_R1.H1
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
