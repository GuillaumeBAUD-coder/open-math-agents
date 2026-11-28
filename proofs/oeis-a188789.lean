import OMAStatements.S_oeis_a188789
import Mathlib

open OMA.S_oeis_a188789

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a188789.main) := by
  intro h
  have h0 := h.2 0
  revert h0
  decide +kernel
