import OMAReductions.R_OeisA135508_conjecture_R1

open OeisA135508 OMA.R_OeisA135508_conjecture_R1

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih => exact ih.trans (x_dvd_succ n (by omega))
