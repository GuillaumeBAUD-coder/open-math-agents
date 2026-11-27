import OMAReductions.R_OeisA234246_conjecture_2_R1

-- Step OeisA234246.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA234246.conjecture_2.R1
-- Credit: @mattdorman
-- H1: at each of the nine listed indices the count a n is one. A finite computation,
-- checked by the kernel at each index.

set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_OeisA234246_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
