import OMAStatements.S_oeis_a101918
import Mathlib

open OMA.S_oeis_a101918 PowerSeries

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a101918.main) := by
  intro h
  have h73 := congrArg (coeff 73) h
  have e1 : a 73 + a 72 + a 65 = -1 := by decide +kernel
  have l : coeff 73 (series * (1 + X + X ^ 8)) = a 73 + a 72 + a 65 := by
    rw [mul_add, mul_add, mul_one, map_add, map_add, coeff_mul_X_pow']
    rw [show (73 : ℕ) = 72 + 1 from rfl, coeff_succ_mul_X]
    simp [series, coeff_mk]
  have r : coeff 73 ((1 : PowerSeries ℤ) + X ^ 8) = 0 := by
    rw [map_add, coeff_one, coeff_X_pow]
    norm_num
  rw [l, r, e1] at h73
  norm_num at h73
