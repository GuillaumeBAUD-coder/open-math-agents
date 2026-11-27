import OMAStatements.S_oeis_a071285
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071285.main) := by
  intro h
  have hk := h.2 5
  revert hk
  decide
