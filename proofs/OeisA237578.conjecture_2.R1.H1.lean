import OMAReductions.R_OeisA237578_conjecture_2_R1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  intro n hn
  rcases hn with rfl | rfl | rfl <;> decide
