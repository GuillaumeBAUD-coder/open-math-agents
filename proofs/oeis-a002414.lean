import OMAStatements.S_oeis_a002414
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a002414.main := by
  have e : (1 - X : PowerSeries ℚ) ^ 4 = 1 - C 4 * X ^ 1 + C 6 * X ^ 2 - C 4 * X ^ 3 + X ^ 4 := by
    simp only [map_ofNat]; ring
  have r : (X : PowerSeries ℚ) * (1 + 5 * X) = C 1 * X ^ 1 + C 5 * X ^ 2 := by
    simp only [map_ofNat, map_one]; ring
  rw [e, r]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mk]
  rw [mul_comm (mk _) (C 4 * X ^ 1), mul_comm (mk _) (C 6 * X ^ 2), mul_comm (mk _) (C 4 * X ^ 3),
    mul_comm (mk _) (X ^ 4), mul_assoc, mul_assoc, mul_assoc, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    coeff_X_pow_mul', coeff_X_pow_mul', coeff_X_pow_mul', coeff_X_pow_mul', coeff_C_mul, coeff_C_mul,
    coeff_X_pow, coeff_X_pow]
  simp only [coeff_mk, OMA.S_oeis_a002414.a]
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> norm_num
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega)]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
      show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
    push_cast
    ring
