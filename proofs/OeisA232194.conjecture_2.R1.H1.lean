import OMAReductions.R_OeisA232194_conjecture_2_R1

set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_OeisA232194_conjecture_2_R1.H1 := by
  intro n hn
  fin_cases hn <;> decide
