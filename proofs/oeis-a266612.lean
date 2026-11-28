import OMAStatements.S_oeis_a266612
import Mathlib

open OMA.S_oeis_a266612 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a266612.main) := by
  intro h
  have h4 := h.2.1 4 (by norm_num)
  have e4 : a 4 = 10100 := by decide
  have e3 : a (4 - 1) = 1010 := by decide
  have e2 : a (4 - 2) = 101 := by decide
  have e1 : a (4 - 3) = 10 := by decide
  rw [e4, e3, e2, e1] at h4
  norm_num at h4
