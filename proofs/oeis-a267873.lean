import OMAStatements.S_oeis_a267873
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267873.main) := by
  intro h
  have h4 := h.1 4 (by norm_num)
  have e4 : OMA.S_oeis_a267873.a 4 = 9 := by decide
  have e3 : OMA.S_oeis_a267873.a 3 = 7 := by decide
  have e2 : OMA.S_oeis_a267873.a 2 = 4 := by decide
  norm_num [e4, e3, e2] at h4
