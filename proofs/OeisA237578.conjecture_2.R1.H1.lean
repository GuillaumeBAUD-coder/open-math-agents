import OMAReductions.R_OeisA237578_conjecture_2_R1

/-! Evaluate the three specified counts using the computable prime-counting function. -/

set_option maxRecDepth 10000 in
theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  intro n hn
  rcases hn with rfl | rfl | rfl
  · exact OeisA237578.a_5
  · decide +kernel
  · decide +kernel
