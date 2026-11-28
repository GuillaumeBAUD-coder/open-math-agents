import OMAStatements.S_oeis_a110320
import Mathlib

open OMA.S_oeis_a110320 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a110320.main := by
  intro S A B Cc _ hS0 hA hB hC n _
  have hS : S ≠ 0 := by
    intro h; rw [h] at hS0; simp at hS0
  have key : (B - X * Cc - 2 * X ^ 2 * A) * S = 2 * S := by
    linear_combination hB - X * hC - hA
  have hB' : B = X * Cc + X ^ 2 * (2 * A) + PowerSeries.C (2 : ℚ) := by
    have := mul_right_cancel₀ hS key
    rw [map_ofNat]
    linear_combination this
  rw [hB']
  have e1 : coeff (n + 2) (X * Cc) = coeff (n + 1) Cc := by
    rw [show n + 2 = (n + 1) + 1 by omega, coeff_succ_X_mul]
  have e2 : coeff (n + 2) (X ^ 2 * (2 * A)) = 2 * coeff n A := by
    rw [coeff_X_pow_mul', if_pos (by omega), show n + 2 - 2 = n by omega,
      ← map_ofNat PowerSeries.C 2, coeff_C_mul]
  rw [map_add, map_add, e1, e2, coeff_C, if_neg (by omega)]
  ring
