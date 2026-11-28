import OMAReductions.R_oeis_a352305_R1
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Finite check: the primes p < 94 with 188 - p prime are 7, 19, 37, 61, 79 (decide in the kernel).

theorem OMA.solution : OMA.R_oeis_a352305_R1.H1 := by
  unfold OMA.R_oeis_a352305_R1.H1
  unfold OMA.S_oeis_a352305.numWays
  set_option maxRecDepth 100000 in decide +kernel
