import OMAStatements.S_oeis_a285666
import Mathlib

/-!
# A285666: the length formula fails at `n = 2`

Starting from `00`, one step gives `001` and a second step gives `001010`, a word of length `6`,
while `2 ^ 2 + 2 ^ 2 = 8`.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a285666.main) := by
  intro h
  have h2 := h 2 (by norm_num)
  revert h2
  decide
