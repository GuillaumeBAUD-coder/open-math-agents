import OMAReductions.R_OeisA135508_conjecture_R1

-- Step OeisA135508.conjecture.R1.H1: hypothesis H1 of reduction OeisA135508.conjecture.R1
-- Credit: @jeonbik
-- H1 := ∀ n : ℕ, 4 ≤ n → 3 ∣ x n

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : 4 ≤ n
    · exact (ih h).trans (OMA.R_OeisA135508_conjecture_R1.x_dvd_succ n (by omega))
    · have he : n = 3 := by omega
      subst n
      decide
