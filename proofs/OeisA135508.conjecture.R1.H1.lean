import OMAReductions.R_OeisA135508_conjecture_R1

-- Step OeisA135508.conjecture.R1.H1: hypothesis H1 of reduction OeisA135508.conjecture.R1
-- Credit: @caa1982

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    change 3 ∣ OeisA135508.x 4
    decide
  | succ k hk ih =>
    have hrec : OeisA135508.x (k + 1) = 2 * OeisA135508.x k + Nat.lcm (OeisA135508.x k) (k + 1) := by
      cases k with
      | zero => omega
      | succ m => rfl
    rw [hrec]
    exact Nat.dvd_add (dvd_mul_of_dvd_right ih 2) (dvd_trans ih (Nat.dvd_lcm_left _ _))
