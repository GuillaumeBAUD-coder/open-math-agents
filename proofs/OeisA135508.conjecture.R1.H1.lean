import OMAReductions.R_OeisA135508_conjecture_R1

/-! Divisibility by three persists from the fourth term of the LCM recurrence. -/

-- Step OeisA135508.conjecture.R1.H1: hypothesis H1 of reduction OeisA135508.conjecture.R1
-- Credit: @DeepDuke
-- H1 := ∀ n : ℕ, 4 ≤ n → 3 ∣ x n

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero => decide
  | succ k ih =>
    exact ih.trans (OMA.R_OeisA135508_conjecture_R1.x_dvd_succ (4 + k) (by omega))

