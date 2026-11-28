import OMAStatements.S_oeis_a147817
import Mathlib

open OMA.S_oeis_a147817 PowerSeries

set_option maxRecDepth 100000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a147817.main := by
  have c2 : ∀ k : ℕ, (k.choose 2 : ℚ) = k * (k - 1) / 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ', Nat.cast_add, ih, Nat.choose_one_right]
      push_cast; ring
  have c3 : ∀ k : ℕ, (k.choose 3 : ℚ) = k * (k - 1) * (k - 2) / 6 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.choose_succ_succ', Nat.cast_add, ih, c2]
      push_cast; ring
  have hc : ∀ k : ℕ, (k.choose 4 : ℚ) = k * (k - 1) * (k - 2) * (k - 3) / 24 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show (4 : ℕ) = 3 + 1 from rfl, Nat.choose_succ_succ', Nat.cast_add, ih, c3]
      push_cast; ring
  refine ⟨?_, ?_⟩
  · have hq : ∀ F : PowerSeries ℚ, F * (1 - X) ^ 9 = F - C (9 : ℚ) * (F * X ^ 1) + C (36 : ℚ) * (F * X ^ 2) - C (84 : ℚ) * (F * X ^ 3) + C (126 : ℚ) * (F * X ^ 4) - C (126 : ℚ) * (F * X ^ 5) + C (84 : ℚ) * (F * X ^ 6) - C (36 : ℚ) * (F * X ^ 7) + C (9 : ℚ) * (F * X ^ 8) - (F * X ^ 9) := by
      intro F; simp only [map_ofNat]; ring
    have hr : (2 * X ^ 4 * (93 + 688 * X + 18 * X ^ 2 + 48 * X ^ 3 - 7 * X ^ 4) : PowerSeries ℚ) = C (186 : ℚ) * X ^ 4 + C (1376 : ℚ) * X ^ 5 + C (36 : ℚ) * X ^ 6 + C (96 : ℚ) * X ^ 7 - C (14 : ℚ) * X ^ 8 := by
      simp only [map_ofNat, map_one, pow_one]; ring
    rw [hq, hr]
    ext n
    simp only [map_add, map_sub, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    by_cases hn : n < 9
    · interval_cases n <;> norm_num [a, Nat.choose]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      simp only [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega, show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega, show m + 9 - 9 = m + 0 by omega, show 1 ≤ m + 9 by omega, show 2 ≤ m + 9 by omega, show 3 ≤ m + 9 by omega, show 4 ≤ m + 9 by omega, show 5 ≤ m + 9 by omega, show 6 ≤ m + 9 by omega, show 7 ≤ m + 9 by omega, show 8 ≤ m + 9 by omega, show 9 ≤ m + 9 by omega, show m + 9 ≠ 0 by omega, show m + 9 ≠ 1 by omega, show m + 9 ≠ 2 by omega, show m + 9 ≠ 3 by omega, show m + 9 ≠ 4 by omega, show m + 9 ≠ 5 by omega, show m + 9 ≠ 6 by omega, show m + 9 ≠ 7 by omega, show m + 9 ≠ 8 by omega, if_true, if_false]
      simp only [a]; push_cast; simp only [hc]; push_cast; ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    simp only [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega, show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega, show m + 9 - 9 = m + 0 by omega]
    have key : ((a (m + 9) : ℤ) : ℚ) = ((9 * a (m + 8) - 36 * a (m + 7) + 84 * a (m + 6) - 126 * a (m + 5) + 126 * a (m + 4) - 84 * a (m + 3) + 36 * a (m + 2) - 9 * a (m + 1) + a (m + 0) : ℤ) : ℚ) := by
      simp only [a]; push_cast; simp only [hc]; push_cast; ring
    exact_mod_cast key
