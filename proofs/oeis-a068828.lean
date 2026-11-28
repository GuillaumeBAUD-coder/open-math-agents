import OMAStatements.S_oeis_a068828
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a068828.main) := by
  intro h
  have := h 0 0 0 0
  simp at this
