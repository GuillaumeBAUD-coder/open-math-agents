import OMAStatements.S_oeis_a138365
import Mathlib

open PowerSeries OMA.S_oeis_a138365 in
theorem OMA.solution : type_of% @OMA.S_oeis_a138365.main := by
  rw [show ((X : ℤ⟦X⟧) + 1) * (X ^ 2 - 11 * X + 1) = 1 - C 10 * X ^ 1 - C 10 * X ^ 2 + X ^ 3 by
    simp; ring, show -X * (X - 10 : ℤ⟦X⟧) = C 10 * X ^ 1 - X ^ 2 by simp; ring]
  ext (_ | _ | _ | _ | n) <;> simp only [mul_sub, mul_add, mul_one, ← mul_assoc, map_add, map_sub,
    coeff_mul_X_pow', coeff_C, coeff_X_pow, coeff_mk, coeff_mul_C] <;>
    simp [a, b] <;> ring
