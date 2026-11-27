import OMAReductions.R_OeisA232194_conjecture_2_R1

/-! Step H1: `a n = 1` for `n ∈ {3, 4, 6, 20, 24}`, by direct computation. -/

theorem OMA.solution : OMA.R_OeisA232194_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
