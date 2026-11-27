import OMAReductions.R_OeisA135508_conjecture_R1

-- Step OeisA135508.conjecture.R1.H1: hypothesis H1 of reduction OeisA135508.conjecture.R1
-- Credit: @YourFriendPollux

open OeisA135508

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  refine Nat.le_induction (by decide) (fun k hk ih => ?_) n hn
  exact dvd_trans ih (OMA.R_OeisA135508_conjecture_R1.x_dvd_succ k (by omega))
