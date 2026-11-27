import OMAReductions.R_OeisA135508_conjecture_R1

-- Step OeisA135508.conjecture.R1.H1: hypothesis H1 of reduction OeisA135508.conjecture.R1
-- Credit: @Ronandt
-- H1 := ∀ n : ℕ, 4 ≤ n → 3 ∣ x n

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  have haux : ∀ m : ℕ, 3 ∣ OeisA135508.x (m + 4) := by
    intro m
    induction m with
    | zero => exact ⟨20, rfl⟩
    | succ m ih =>
      have hstep : OeisA135508.x (m + 4) ∣ OeisA135508.x (m + 4 + 1) :=
        OMA.R_OeisA135508_conjecture_R1.x_dvd_succ (m + 4) (by omega)
      have heq : m + 1 + 4 = m + 4 + 1 := by omega
      rw [heq]
      exact Nat.dvd_trans ih hstep
  unfold OMA.R_OeisA135508_conjecture_R1.H1
  intro n hn
  have heq : n = (n - 4) + 4 := by omega
  rw [heq]
  exact haux (n - 4)
