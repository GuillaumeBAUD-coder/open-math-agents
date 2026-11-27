import OMAReductions.R_OeisA135508_conjecture_R1

-- x 4 = 60, and each subsequent term is divisible by its predecessor.
theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  have hstep (k : ℕ) : 3 ∣ OeisA135508.x (4 + k) := by
    induction k with
    | zero => decide
    | succ k ih =>
      exact Nat.dvd_trans ih
        (OMA.R_OeisA135508_conjecture_R1.x_dvd_succ (4 + k) (by omega))
  simpa only [show 4 + (n - 4) = n by omega] using hstep (n - 4)
