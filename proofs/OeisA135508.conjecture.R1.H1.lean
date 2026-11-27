import OMAReductions.R_OeisA135508_conjecture_R1

/-!
Every term from index four onward in the LCM recurrence is divisible by three.
Credit: @MicahJank
-/

open OeisA135508

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    exact ih.trans (OMA.R_OeisA135508_conjecture_R1.x_dvd_succ n (by omega))
