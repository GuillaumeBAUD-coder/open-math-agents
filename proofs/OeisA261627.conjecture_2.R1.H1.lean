import OMAReductions.R_OeisA261627_conjecture_2_R1

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
theorem OMA.solution : OMA.R_OeisA261627_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
