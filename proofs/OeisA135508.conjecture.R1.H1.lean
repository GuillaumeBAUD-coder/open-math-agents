import OMAReductions.R_OeisA135508_conjecture_R1

-- Step OeisA135508.conjecture.R1.H1: hypothesis H1 of reduction OeisA135508.conjecture.R1
-- Credit: @OrangeHeadz
-- H1 := ∀ n : ℕ, 4 ≤ n → 3 ∣ x n

/-! # `3 ∣ x n` for `n ≥ 4`

`x 4 = 60` is divisible by `3`, and `x (n + 1) = 2 * x n + lcm (x n) (n + 1)` is a sum of two
multiples of `x n`, so divisibility by `3` propagates. -/

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    show 3 ∣ 2 * OeisA135508.x (k + 1) + Nat.lcm (OeisA135508.x (k + 1)) (k + 1 + 1)
    exact dvd_add (dvd_mul_of_dvd_right ih 2) (ih.trans (Nat.dvd_lcm_left _ _))
