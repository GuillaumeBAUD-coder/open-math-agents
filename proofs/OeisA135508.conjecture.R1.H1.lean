import OMAReductions.R_OeisA135508_conjecture_R1

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
      exact ih.trans (OMA.R_OeisA135508_conjecture_R1.x_dvd_succ k (by omega))
