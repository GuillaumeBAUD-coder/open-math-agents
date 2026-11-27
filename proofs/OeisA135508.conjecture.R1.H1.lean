import OMAReductions.R_OeisA135508_conjecture_R1

/-! Credit: Hanan Beer (@hananzlt).
Divisibility by three propagates from the fourth term.
Uses x_dvd_succ from the reduction by @harshshah1618. -/
theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    exact dvd_trans ih (OMA.R_OeisA135508_conjecture_R1.x_dvd_succ n (by omega))
