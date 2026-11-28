import OMAStatements.S_oeis_a324036
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: a is affine on each residue class mod 4 (n = 4j: 1+6j; n = 4j+2: 2j+1; odd n: 3n+2), so a(n) - 2a(n-4) + a(n-8) = 0; split_ifs and omega.

theorem OMA.solution : type_of% @OMA.S_oeis_a324036.main := by
  intro n hn
  simp only [OMA.S_oeis_a324036.a]
  split_ifs <;> omega
