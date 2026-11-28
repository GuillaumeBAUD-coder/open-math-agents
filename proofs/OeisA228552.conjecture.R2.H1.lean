import OMAReductions.R_OeisA228552_conjecture_R2

theorem OMA.solution : OMA.R_OeisA228552_conjecture_R2.H1 := by
  intro n h
  exact Nat.sqrt_pos.mpr (Int.natAbs_pos.mpr h)