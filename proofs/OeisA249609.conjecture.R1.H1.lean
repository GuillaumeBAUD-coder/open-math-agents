import OMAReductions.R_OeisA249609_conjecture_R1

-- Step OeisA249609.conjecture.R1.H1: hypothesis H1 of reduction OeisA249609.conjecture.R1
-- Credit: @hayalows
--
-- The finite direction of the conjecture: at each of the five listed rows of Pascal's
-- triangle every binomial coefficient is odious, so the least evil entry does not exist and
-- a vanishes. Each value is a direct kernel computation of the binary digit count, so the
-- whole step is discharged by `decide +kernel` after splitting the membership hypothesis.

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem OMA.solution : OMA.R_OeisA249609_conjecture_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
