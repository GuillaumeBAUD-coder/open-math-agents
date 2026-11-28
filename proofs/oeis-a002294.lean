import OMAStatements.S_oeis_a002294
import Mathlib

-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- At n = 2 exactly five words qualify (not 28/7 = 4), so the formula fails.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a002294.main) := by
  intro h
  have h2 := h 2
  revert h2
  decide +kernel
