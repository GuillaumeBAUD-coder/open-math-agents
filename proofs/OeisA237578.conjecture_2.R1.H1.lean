import OMAReductions.R_OeisA237578_conjecture_2_R1

/-! # The three listed prime-counting examples -/

set_option maxRecDepth 10000 in
theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  intro n hn
  rcases hn with rfl | rfl | rfl <;> decide +kernel
