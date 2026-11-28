import OMAReductions.R_oeis_a131629_R1
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Direct computation: the decimal digits of 3^84 are evaluated by norm_num and contain no 3.

theorem OMA.solution : OMA.R_oeis_a131629_R1.H1 := by
  unfold OMA.R_oeis_a131629_R1.H1
  norm_num
