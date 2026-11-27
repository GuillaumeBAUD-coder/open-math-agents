import OMAReductions.R_OeisA135508_conjecture_R1

/-! The 3-divisibility step of the A135508 reduction: after x(4) = 60, the recursion
x(n+1) = 2 x(n) + lcm(x(n), n+1) keeps the factor 3. -/

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  refine Nat.le_induction ?base ?step n hn
  · decide
  · intro k hk ih
    exact dvd_trans ih (OMA.R_OeisA135508_conjecture_R1.x_dvd_succ k (by omega))
