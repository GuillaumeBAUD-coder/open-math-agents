import OMAStatements.S_mo_261486
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_261486.main) := by
  intro h
  have h136 := h 136 (by norm_num) 11 (by norm_num)
  exact h136 (by
    unfold OMA.S_mo_261486.d
    norm_num)
