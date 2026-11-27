import OMAStatements.S_oeis_a059837
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a059837.main) := by
  intro h
  have h0 := h 0
  norm_num [OMA.S_oeis_a059837.diagonal, Nat.factorial, Nat.choose] at h0
