import OMAStatements.S_oeis_a001845
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: Expand (1-X)^4 and (1+X)^3 and compare coefficients (coeff_mul_X_pow'): n < 4 by computation, and for n+4 the fourth difference of the cubic a vanishes (ring).

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a001845.main := by
  have e1 : PowerSeries.mk OMA.S_oeis_a001845.a * (1 - X) ^ 4 =
      PowerSeries.mk OMA.S_oeis_a001845.a - C 4 * (PowerSeries.mk OMA.S_oeis_a001845.a * X ^ 1)
        + C 6 * (PowerSeries.mk OMA.S_oeis_a001845.a * X ^ 2)
        - C 4 * (PowerSeries.mk OMA.S_oeis_a001845.a * X ^ 3)
        + PowerSeries.mk OMA.S_oeis_a001845.a * X ^ 4 := by
    simp only [map_ofNat]; ring
  have e2 : (1 + X : PowerSeries ℚ) ^ 3 = 1 + C 3 * X + C 3 * X ^ 2 + X ^ 3 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one,
    coeff_X, coeff_mk]
  rcases n with _ | _ | _ | _ | n
  · simp [OMA.S_oeis_a001845.a]
  · simp [OMA.S_oeis_a001845.a]; norm_num
  · simp [OMA.S_oeis_a001845.a]; norm_num
  · simp [OMA.S_oeis_a001845.a]; norm_num
  · simp only [OMA.S_oeis_a001845.a]
    simp
    push_cast
    ring
