import OMAStatements.S_oeis_a267186
import Mathlib

open OMA.S_oeis_a267186
open PowerSeries

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267186.main) := by
  rintro ⟨h, -⟩
  have h6 := h 6 (by norm_num)
  have v6 : a 6 = 2 := by simp [a, T]
  have v5 : a 5 = 6 := by simp [a, T]
  have v3 : a 3 = 0 := by simp [a, T]
  have v2 : a 2 = 3 := by simp [a, T]
  norm_num [v6, v5, v3, v2] at h6
