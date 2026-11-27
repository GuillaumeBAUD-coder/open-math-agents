import OMAReductions.R_OeisA234246_conjecture_2_R1

-- Step OeisA234246.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA234246.conjecture_2.R1
-- Credit: @Ciphore
-- H1 := ∀ n : ℕ, n ∈ ({4, 5, 8, 9, 12, 13, 24, 33, 49} : Finset ℕ) → OeisA234246.a n = 1  /-- The open direction: count one happens only at the nine listed indices. -/

set_option maxHeartbeats 2000000000 in
set_option maxRecDepth 1000000 in
theorem OMA.solution : OMA.R_OeisA234246_conjecture_2_R1.H1 := by
  intro n hn
  simp at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

