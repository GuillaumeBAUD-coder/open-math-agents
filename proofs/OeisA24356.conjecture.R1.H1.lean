import OMAReductions.R_OeisA24356_conjecture_R1

-- Step H1 of reductions/OeisA24356.conjecture.R1.lean: the Hankel determinant of the primes
-- 2, 3, 5, 7, 11, 13, 17 vanishes, with (6, -3, -2, 1) in its kernel. The upstream module
-- certifies this as OeisA24356.a_4 (kernel-checked, no native_decide).

theorem OMA.solution : OMA.R_OeisA24356_conjecture_R1.H1 := by
  exact OeisA24356.a_4
