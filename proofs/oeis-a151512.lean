import OMAStatements.S_oeis_a151512
import Mathlib

/-!
# A151512: the three claims contradict each other

The first claim with `j = 5`, `i = 2` says `A151512 4 1 = eqRel 4 3`.  The second claim gives
`A151512 4 1 = 6` and the third gives `eqRel 4 3 = 7`.  (Indeed there are `S(4, 3) = 6`
partitions of a four-element set into three blocks, not `7`.)
-/

open OMA.S_oeis_a151512 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a151512.main) := by
  rintro ⟨h1, ⟨-, h41, -, -, -⟩, h3⟩
  have h := h1 5 2 (by norm_num) (by norm_num)
  have e1 : 5 - 1 = 4 := rfl
  have e2 : 2 - 1 = 1 := rfl
  have e3 : 5 - 2 = 3 := rfl
  rw [e1, e2, e3, h41, h3] at h
  omega
