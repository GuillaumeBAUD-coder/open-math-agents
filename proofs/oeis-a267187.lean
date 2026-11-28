import OMAStatements.S_oeis_a267187
import Mathlib

open OMA.S_oeis_a267187
open PowerSeries

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267187.main) := by
  rintro ⟨h, -⟩
  have h8 := h 8 (by norm_num)
  have v8 : a 8 = 2 := by simp [a, T]
  have v7 : a 7 = 7 := by simp [a, T]
  have v4 : a 4 = 0 := by simp [a, T]
  have v3 : a 3 = 4 := by simp [a, T]
  norm_num [v8, v7, v4, v3] at h8
