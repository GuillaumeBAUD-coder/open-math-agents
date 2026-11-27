import OMAReductions.R_OeisA135508_conjecture_R1

-- Step OeisA135508.conjecture.R1.H1: hypothesis H1 of reduction OeisA135508.conjecture.R1
-- Credit: @ihateSAS
-- H1 := ∀ n : ℕ, 4 ≤ n → 3 ∣ x n
--
-- `x (n+1) = x n * (2 + (n+1)/gcd (x n) (n+1))`, so the sequence is divisibility increasing.
-- Since `x 4 = 60` is a multiple of 3, every later term is too.

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  have h4 : (3 : ℕ) ∣ OeisA135508.x 4 := by decide
  have key : ∀ k : ℕ, OeisA135508.x 4 ∣ OeisA135508.x (4 + k) := by
    intro k
    induction k with
    | zero => exact dvd_refl _
    | succ k ih =>
      have h := OMA.R_OeisA135508_conjecture_R1.x_dvd_succ (4 + k) (by omega)
      exact ih.trans h
  have e : 4 + (n - 4) = n := by omega
  rw [← e]
  exact dvd_trans h4 (key (n - 4))
