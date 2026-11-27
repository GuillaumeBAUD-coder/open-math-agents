import OMAReductions.R_OeisA135508_conjecture_R1

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    have hx4 : OeisA135508.x 4 = 60 := by decide
    rw [hx4]
    decide
  | succ k hk ih =>
    exact ih.trans (OMA.R_OeisA135508_conjecture_R1.x_dvd_succ k (by omega))
