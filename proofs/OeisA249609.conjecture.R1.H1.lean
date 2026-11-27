import OMAReductions.R_OeisA249609_conjecture_R1

-- Step OeisA249609.conjecture.R1.H1 of A249609
-- The finite direction: rows 0, 1, 2, 7, 8 of Pascal's triangle are entirely odious.
-- Each case is a direct computation of the binomial row and its binary digit counts.

theorem OMA.solution : OMA.R_OeisA249609_conjecture_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
