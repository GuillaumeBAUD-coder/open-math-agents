import OMAReductions.R_OeisA135508_conjecture_R1

-- Step OeisA135508.conjecture.R1.H1: hypothesis H1 of reduction OeisA135508.conjecture.R1
-- Credit: @ivillar
-- H1 := ∀ n : ℕ, 4 ≤ n → 3 ∣ x n
-- Proof: x 4 = 60 is a multiple of 3, and for n ≥ 1 the recurrence
-- x (n + 1) = 2 * x n + lcm (x n) (n + 1) gives a multiple of x n, so 3 ∣ x n propagates.

open OeisA135508

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  unfold OMA.R_OeisA135508_conjecture_R1.H1
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact ⟨20, rfl⟩
  | succ n hn ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    change 3 ∣ 2 * x (m + 1) + Nat.lcm (x (m + 1)) (m + 1 + 1)
    exact dvd_add (dvd_mul_of_dvd_right ih 2) (ih.trans (Nat.dvd_lcm_left _ _))
