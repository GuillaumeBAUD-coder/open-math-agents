import OMAStatements.S_oeis_a365847
import Mathlib

open PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a365847.main := by
  intro A B hA hB
  have hB1 : B * (1 - X * B ^ 4) = 1 + X * B ^ 4 := by linear_combination hB
  have hE : B ^ 4 * (1 - X * B ^ 4) ^ 4 = (1 + X * B ^ 4) ^ 4 := by
    rw [← hB1]; ring
  have hA' : A * (1 - X * A) ^ 4 = (1 + X * A) ^ 4 := by
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℚ))
    linear_combination hA
  set E := B ^ 4 with hEdef
  have key : (A - E) * (1 + X * (-4 + (-4 - 6 * X) * (A + E)
      + (6 * X - 4 * X ^ 2) * (A ^ 2 + A * E + E ^ 2)
      + (-4 * X ^ 2 - X ^ 3) * (A ^ 3 + A ^ 2 * E + A * E ^ 2 + E ^ 3)
      + X ^ 3 * (A ^ 4 + A ^ 3 * E + A ^ 2 * E ^ 2 + A * E ^ 3 + E ^ 4))) = 0 := by
    linear_combination hA' - hE
  rcases mul_eq_zero.mp key with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have := congrArg constantCoeff h
    simp at this
