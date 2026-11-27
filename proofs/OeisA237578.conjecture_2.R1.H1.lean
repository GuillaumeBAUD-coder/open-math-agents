import OMAReductions.R_OeisA237578_conjecture_2_R1

-- Step OeisA237578.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA237578.conjecture_2.R1
-- Credit: @YourFriendPollux

set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  unfold OMA.R_OeisA237578_conjecture_2_R1.H1
  intro n hn
  rcases hn with rfl | rfl | rfl <;> decide
