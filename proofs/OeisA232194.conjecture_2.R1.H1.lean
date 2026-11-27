import OMAReductions.R_OeisA232194_conjecture_2_R1

-- Step OeisA232194.conjecture_2.R1.H1
-- Credit: @caa1982

set_option maxRecDepth 200000 in
theorem OMA.solution : OMA.R_OeisA232194_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
