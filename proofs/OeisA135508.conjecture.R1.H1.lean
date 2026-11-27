import OMAReductions.R_OeisA135508_conjecture_R1

-- Step OeisA135508.conjecture.R1.H1: hypothesis H1 of reduction OeisA135508.conjecture.R1
-- Credit: @anmolspace
-- Proof: x 4 = 60 is divisible by 3, and x (n+1) = 2 * x n + lcm (x n) (n+1) for n >= 1,
-- where both summands are multiples of x n; induct from 4.

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have e : OeisA135508.x (k + 1 + 1)
        = 2 * OeisA135508.x (k + 1) + Nat.lcm (OeisA135508.x (k + 1)) (k + 1 + 1) := rfl
    rw [e]
    exact Dvd.dvd.add (Dvd.dvd.mul_left ih 2) (ih.trans (Nat.dvd_lcm_left _ _))
