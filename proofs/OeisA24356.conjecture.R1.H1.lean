import OMAReductions.R_OeisA24356_conjecture_R1

/-! Evaluate the fourth prime Hankel determinant by cofactor expansion. -/

-- Step OeisA24356.conjecture.R1.H1: hypothesis H1 of reduction OeisA24356.conjecture.R1
-- Credit: @DeepDuke
-- H1 := OeisA24356.a 4 = 0  /-- The uniqueness direction: `4` is the only index at which the sequence vanishes. -/

theorem OMA.solution : OMA.R_OeisA24356_conjecture_R1.H1 := by
  exact OeisA24356.a_4
