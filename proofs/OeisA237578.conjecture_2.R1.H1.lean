import OMAReductions.R_OeisA237578_conjecture_2_R1

-- Step OeisA237578.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA237578.conjecture_2.R1
-- Credit: @ivillar
-- Proof: a finite computation. a n counts the 0 < k < n with primeCounting (k * n) prime, which
-- for n = 5, 8, 13 involves primeCounting below 13 * 13; the kernel evaluates it (decide +kernel).

theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  unfold OMA.R_OeisA237578_conjecture_2_R1.H1
  rintro n (rfl | rfl | rfl) <;> decide +kernel
