import OMAStatements.S_oeis_a071281
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071281.main) := by
  intro h
  have hk := h.2 3
  revert hk
  decide
