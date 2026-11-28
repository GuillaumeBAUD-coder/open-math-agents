import OMAStatements.S_oeis_a145920
import Mathlib

open OMA.S_oeis_a145920 PowerSeries

theorem xk (k r : ℕ) : x (2 * k + r) = ((k + r / 2 : ℕ) : ℚ) * (-1) ^ r := by
  unfold x
  rw [show (2 * k + r) / 2 = k + r / 2 by omega, pow_add, pow_mul]
  norm_num

theorem xk0 (k : ℕ) : x (2 * k) = (k : ℚ) := by
  have := xk k 0
  simpa using this

theorem R (m : ℕ) : a (m + 9) - a (m + 8) - 4 * a (m + 7) + 4 * a (m + 6) + 6 * a (m + 5) -
    6 * a (m + 4) - 4 * a (m + 3) + 4 * a (m + 2) + a (m + 1) - a m = 0 := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · simp only [a, xk, xk0]
    norm_num
    ring
  · simp only [add_assoc, Nat.reduceAdd, a, xk]
    norm_num
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a145920.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    have := R m
    simp only [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega,
      show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega,
      show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega,
      show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega,
      show m + 9 - 9 = m by omega]
    linear_combination this
  · have hq : ∀ F : PowerSeries ℚ, F * ((1 + X) ^ 4 * (1 - X) ^ 5) = F - (F * X ^ 1) - C (4 : ℚ) * (F * X ^ 2) + C (4 : ℚ) * (F * X ^ 3) + C (6 : ℚ) * (F * X ^ 4) - C (6 : ℚ) * (F * X ^ 5) - C (4 : ℚ) * (F * X ^ 6) + C (4 : ℚ) * (F * X ^ 7) + (F * X ^ 8) - (F * X ^ 9) := by
      intro F; simp only [map_ofNat, map_one, pow_one]; ring
    have hr : (X ^ 2 * (1 + 4 * X + 26 * X ^ 2 + 19 * X ^ 3 + 26 * X ^ 4 + 4 * X ^ 5 + X ^ 6) : PowerSeries ℚ) = X ^ 2 + C (4 : ℚ) * X ^ 3 + C (26 : ℚ) * X ^ 4 + C (19 : ℚ) * X ^ 5 + C (26 : ℚ) * X ^ 6 + C (4 : ℚ) * X ^ 7 + X ^ 8 := by
      simp only [map_ofNat, map_one, pow_one]; ring
    rw [hq, hr]
    ext n
    simp only [map_add, map_sub, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    by_cases hn : n < 9
    · interval_cases n <;> norm_num [a, x]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      simp only [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega, show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega, show m + 9 - 9 = m + 0 by omega, show 1 ≤ m + 9 by omega, show 2 ≤ m + 9 by omega, show 3 ≤ m + 9 by omega, show 4 ≤ m + 9 by omega, show 5 ≤ m + 9 by omega, show 6 ≤ m + 9 by omega, show 7 ≤ m + 9 by omega, show 8 ≤ m + 9 by omega, show 9 ≤ m + 9 by omega, show m + 9 ≠ 0 by omega, show m + 9 ≠ 1 by omega, show m + 9 ≠ 2 by omega, show m + 9 ≠ 3 by omega, show m + 9 ≠ 4 by omega, show m + 9 ≠ 5 by omega, show m + 9 ≠ 6 by omega, show m + 9 ≠ 7 by omega, show m + 9 ≠ 8 by omega, if_true, if_false]
      norm_num; linear_combination R m

