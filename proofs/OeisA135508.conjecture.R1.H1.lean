import OMAReductions.R_OeisA135508_conjecture_R1

-- Step OeisA135508.conjecture.R1.H1: hypothesis H1 of reduction OeisA135508.conjecture.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ n : ℕ, 4 ≤ n → 3 ∣ x n

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hx : OeisA135508.x (m + 1 + 1) =
        2 * OeisA135508.x (m + 1) + Nat.lcm (OeisA135508.x (m + 1)) (m + 1 + 1) := by
      simp [OeisA135508.x]
    rw [hx]
    exact dvd_add (dvd_mul_of_dvd_right ih 2) (ih.trans (Nat.dvd_lcm_left _ _))
