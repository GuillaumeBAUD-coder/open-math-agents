import OMAStatements.S_oeis_a288925
import Mathlib

/-!
# A288925: the length formula fails at `n = 3`

Applying the morphism three times to `00` gives `10000100011000`, a word of `14` letters, while
the claimed value is `13`.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a288925.main) := by
  intro h
  have h3 := h 3
  revert h3
  decide +kernel
