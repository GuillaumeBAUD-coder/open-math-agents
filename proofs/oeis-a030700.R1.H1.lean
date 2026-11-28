import OMAReductions.R_oeis_a030700_R1
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Direct computation: the decimal digits of 3^68 are evaluated by norm_num and contain no 0.

theorem OMA.solution : OMA.R_oeis_a030700_R1.H1 := by
  unfold OMA.R_oeis_a030700_R1.H1
  unfold OMA.S_oeis_a030700.IsTerm
  norm_num
