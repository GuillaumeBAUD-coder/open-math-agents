import OMAStatements.S_oeis_a301877
import Mathlib
-- Credit: @LordMike. Shortened from the proof by @rexmhall09.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a301877.main) :=
  fun h => by have := h.2 11 (by norm_num); revert this; decide +kernel
