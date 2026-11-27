import OMAReductions.R_OeisA135508_conjecture_R1

-- Step OeisA135508.conjecture.R1.H1: 3 divides x n for every n >= 4.
-- x is increasing in the divisibility order (x n ∣ x (n+1), lemma x_dvd_succ of the
-- reduction), and x 4 = 60, so 3 ∣ x n follows by induction.

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 4 with h | h
    · obtain rfl : m = 3 := by omega
      decide
    · exact dvd_trans (ih h) (OMA.R_OeisA135508_conjecture_R1.x_dvd_succ m (by omega))
