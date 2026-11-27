import OMAReductions.R_OeisA232194_conjecture_2_R1

-- Step OeisA232194.conjecture_2.R1.H1 of A232194
-- The finite direction: at 3, 4, 6, 20 and 24 the count is one.
-- Each case is a direct computation of the sum defining `a` on that value.

set_option maxRecDepth 10000 in
theorem OMA.solution : OMA.R_OeisA232194_conjecture_2_R1.H1 := by
  intro n hn
  fin_cases hn <;> decide
