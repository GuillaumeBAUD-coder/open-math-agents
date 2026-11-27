import OMAReductions.R_OeisA237578_conjecture_2_R1

/-! The three values `a 5`, `a 8`, `a 13` are each computed in the kernel. -/

theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  rintro n (rfl | rfl | rfl) <;> decide +kernel
