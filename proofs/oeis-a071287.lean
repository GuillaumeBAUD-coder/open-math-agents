import OMAStatements.S_oeis_a071287
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071287.main) := by
  intro h
  have hk := h.2 6
  revert hk
  decide
