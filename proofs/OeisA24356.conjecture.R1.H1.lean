import OMAReductions.R_OeisA24356_conjecture_R1

-- Step OeisA24356.conjecture.R1.H1: hypothesis H1 of reduction OeisA24356.conjecture.R1
-- Credit: @hayalows
--
-- H1 is the existence direction of OeisA24356.conjecture: the Hankel determinant of the first
-- seven primes vanishes at index 4. The upstream module already proves exactly this as
-- OeisA24356.a_4, so the step is a direct restatement.

theorem OMA.solution : OMA.R_OeisA24356_conjecture_R1.H1 := by
  unfold OMA.R_OeisA24356_conjecture_R1.H1
  exact OeisA24356.a_4
