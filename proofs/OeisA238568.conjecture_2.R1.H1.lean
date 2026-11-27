import OMAReductions.R_OeisA238568_conjecture_2_R1

-- Step OeisA238568.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA238568.conjecture_2.R1
-- Credit: @hayalows
--
-- The finite direction of conjecture (i): at each of the seven listed indices the count of
-- k with n ^ 2 - pi (k * n) prime is one. Each value is a direct kernel computation of the
-- prime counting function, so the whole step is discharged by `decide +kernel` after
-- splitting the membership hypothesis.

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem OMA.solution : OMA.R_OeisA238568_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
