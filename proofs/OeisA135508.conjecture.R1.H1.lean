import OMAReductions.R_OeisA135508_conjecture_R1

-- Step OeisA135508.conjecture.R1.H1
-- Credit: @nijv

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  unfold OMA.R_OeisA135508_conjecture_R1.H1
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero => decide
  | succ k ih =>
    exact dvd_trans ih (OMA.R_OeisA135508_conjecture_R1.x_dvd_succ (4 + k) (by omega))
