import OMAReductions.R_OeisA232194_conjecture_2_R1

-- Step OeisA232194.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA232194.conjecture_2.R1
-- Credit: @anmolspace
-- Proof: the five values a 3, a 4, a 6, a 20, a 24 are computed by decide.

set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_OeisA232194_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
