import OMAStatements.S_mo_196613
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_196613.main) := by
  intro h
  have h1 := h 1 one_ne_zero 0 (Or.inr (by simp [OMA.S_mo_196613.xi]))
  norm_num at h1
