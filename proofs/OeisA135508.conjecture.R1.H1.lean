import OMAReductions.R_OeisA135508_conjecture_R1

/-! # Divisibility by three persists in the auxiliary sequence -/

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : 4 ≤ n
    · exact (ih h).trans (OMA.R_OeisA135508_conjecture_R1.x_dvd_succ n (by omega))
    · have heq : n + 1 = 4 := by omega
      rw [heq]
      decide
