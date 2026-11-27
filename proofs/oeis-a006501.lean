import OMAStatements.S_oeis_a006501
import Mathlib

open OMA.S_oeis_a006501 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a006501.main := by
  intro n
  have h : seriesA = seriesB + X ^ 2 * seriesB := by
    have e : ((1 - X) ^ 2 * (1 - X ^ 3) ^ 2 : PowerSeries ℚ) = (1 - X) ^ 4 * (1 + X + X ^ 2) ^ 2 := by
      ring
    rw [seriesA, seriesB, e]
    ring
  rw [h, map_add, coeff_X_pow_mul']
