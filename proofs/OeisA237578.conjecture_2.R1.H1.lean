import OMAReductions.R_OeisA237578_conjecture_2_R1

/-! Step H1: `a n = 1` for `n ∈ {5, 8, 13}`, by direct computation. -/

theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  rintro n (rfl | rfl | rfl) <;> decide +kernel
