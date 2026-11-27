import OMAReductions.R_OeisA237578_conjecture_2_R1

-- Step OeisA237578.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA237578.conjecture_2.R1
-- Credit: @DeepDuke
-- H1 := ∀ n : ℕ, (n = 5 ∨ n = 8 ∨ n = 13) → OeisA237578.a n = 1  /-- The open direction: count one happens only at the three listed indices. -/

set_option maxRecDepth 10000 in
theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  intro n hn
  rcases hn with rfl | rfl | rfl <;> decide

