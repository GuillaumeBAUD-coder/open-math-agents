import OMAReductions.R_OeisA238568_conjecture_2_R1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem OMA.solution : OMA.R_OeisA238568_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
