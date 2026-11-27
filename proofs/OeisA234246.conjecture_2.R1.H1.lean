import OMAReductions.R_OeisA234246_conjecture_2_R1

-- Step OeisA234246.conjecture_2.R1.H1 of A234246
-- The finite direction: at each of the nine listed indices the count is one.
-- Each case is a direct computation of the totients and squares involved.

set_option maxRecDepth 20000 in
theorem OMA.solution : OMA.R_OeisA234246_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
