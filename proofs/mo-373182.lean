import OMAStatements.S_mo_373182
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_373182.main := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ a ha
  rw [IntermediateField.isSeparable_adjoin_simple_iff_isSeparable]
  exact IsSeparable.of_algebra_isSeparable_of_isSeparable K ha
