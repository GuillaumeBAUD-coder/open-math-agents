import OMAReductions.R_OeisA237578_conjecture_2_R1

-- Step OeisA237578.conjecture_2.R1.H1 of A237578
-- The finite direction: at 5, 8 and 13 the count is one.
-- Each case is a direct computation of the prime counting function on finitely many products.

set_option maxRecDepth 10000 in
theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  intro n hn
  rcases hn with rfl | rfl | rfl <;> decide
