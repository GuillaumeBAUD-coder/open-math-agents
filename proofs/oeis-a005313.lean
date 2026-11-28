import OMAStatements.S_oeis_a005313
import Mathlib

open OMA.S_oeis_a005313 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a005313.main := by
  have hq : ∀ F : PowerSeries ℚ, F * ((1 - 3 * X + X ^ 2) * (1 + X) * (1 - X) ^ 2) = F - C (4 : ℚ) * (F * X ^ 1) + C (3 : ℚ) * (F * X ^ 2) + C (3 : ℚ) * (F * X ^ 3) - C (4 : ℚ) * (F * X ^ 4) + (F * X ^ 5) := by
    intro F; simp only [map_ofNat, map_one, pow_one]; ring
  have hr : (X * (1 - X - 3 * X ^ 2 + X ^ 3) : PowerSeries ℚ) = X ^ 1 - X ^ 2 - C (3 : ℚ) * X ^ 3 + X ^ 4 := by
    simp only [map_ofNat, map_one, pow_one]; ring
  rw [hq, hr]
  ext n
  simp only [map_add, map_sub, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
  by_cases hn : n < 5
  · interval_cases n <;> norm_num [a, Finset.sum_range_succ, Nat.fib_add_two]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m + 0 by omega, show 1 ≤ m + 5 by omega, show 2 ≤ m + 5 by omega, show 3 ≤ m + 5 by omega, show 4 ≤ m + 5 by omega, show 5 ≤ m + 5 by omega, show m + 5 ≠ 0 by omega, show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega, show m + 5 ≠ 3 by omega, show m + 5 ≠ 4 by omega, if_true, if_false]
    simp only [a, Finset.sum_range_succ, Nat.fib_add_two, show m + 0 = m by omega]
    push_cast
    ring
