import OMAReductions.R_OeisA234246_conjecture_2_R1

-- Step OeisA234246.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA234246.conjecture_2.R1
-- Credit: @YourFriendPollux



set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_OeisA234246_conjecture_2_R1.H1 := by
  unfold OMA.R_OeisA234246_conjecture_2_R1.H1
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
