import OMAStatements.S_oeis_a068828
import Mathlib

/-!
# Equal inputs disprove the outer equivalence

The left side of the equivalence is an implication beginning with p less than q.
Taking all four inputs to be zero makes this implication vacuously true.
The right side becomes the false strict inequality zero less than zero.
-/

namespace OMA.S_oeis_a068828
end OMA.S_oeis_a068828

open OMA.S_oeis_a068828 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a068828.main) := by
  intro h
  simpa using h 0 0 0 0
