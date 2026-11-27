import OMAReductions.R_OeisA261627_conjecture_2_R1

-- Step OeisA261627.conjecture_2.R1.H1 of A261627
-- The finite direction: at 5, 7, 10, 11, 12, 19, 22, 30, 34, 44, 46, 72 and 142 the count
-- of admissible primes is one.  Each case is a direct computation of the filter defining `a`.

set_option maxRecDepth 10000 in
theorem OMA.solution : OMA.R_OeisA261627_conjecture_2_R1.H1 := by
  intro n hn
  fin_cases hn <;> decide
