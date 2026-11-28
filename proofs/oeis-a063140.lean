import OMAStatements.S_oeis_a063140
import Mathlib

namespace OMA.S_oeis_a063140
open PowerSeries

theorem aux : PowerSeries.mk (fun n => (a n : ℚ) / (n.factorial : ℚ)) =
    20 + X + 4 * PowerSeries.exp ℚ * (6 * X - 5) := by
  have h1 : (20 + X + 4 * PowerSeries.exp ℚ * (6 * X - 5) : PowerSeries ℚ)
      = PowerSeries.C (20 : ℚ) + X + (PowerSeries.C (24 : ℚ) * (PowerSeries.exp ℚ * X)
        - PowerSeries.C (20 : ℚ) * PowerSeries.exp ℚ) := by
    simp only [map_ofNat]
    ring
  rw [h1]
  ext n
  rcases n with _ | _ | n
  · simp [a, coeff_C, coeff_X, PowerSeries.coeff_exp]
  · simp [a, coeff_C, coeff_X, PowerSeries.coeff_exp, coeff_succ_mul_X, mul_comm]
    norm_num
  · have hX : PowerSeries.coeff (n + 1 + 1) (PowerSeries.exp ℚ * X) = 1 / ((n + 1).factorial : ℚ) := by
      rw [mul_comm, PowerSeries.coeff_succ_X_mul]
      simp [PowerSeries.coeff_exp]
    rw [map_add, map_add, map_sub, coeff_C_mul, coeff_C_mul, hX]
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_exp, a, coeff_C, coeff_X]
    simp
    rw [Nat.factorial_succ (n + 1), Nat.factorial_succ n]
    push_cast
    field_simp
end OMA.S_oeis_a063140

theorem OMA.solution : type_of% @OMA.S_oeis_a063140.main := OMA.S_oeis_a063140.aux
