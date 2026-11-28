import OMAStatements.S_oeis_a071722

namespace OMA.P_oeis_a071722

open OMA.S_oeis_a071722 PowerSeries

lemma X_mul_C_sq : (X : PowerSeries ℤ) * catGF ^ 2 = catGF - 1 := by
  ext n
  cases n with
  | zero => simp [catGF]
  | succ n =>
    rw [coeff_succ_X_mul, pow_two, coeff_mul]
    simp only [catGF, coeff_mk, map_sub, coeff_one, Nat.succ_ne_zero, if_false, sub_zero]
    rw [catalan_succ']
    push_cast
    rfl

lemma X_pow_three_mul :
    (X : PowerSeries ℤ) ^ 3 * ((1 + X ^ 2 * catGF ^ 2) * catGF ^ 3) =
      X * catGF + X * catGF - 4 * (X * (X * catGF)) + X * (X * (X * catGF)) - 2 * X + 2 * X ^ 2 := by
  linear_combination
    X * ((X * catGF) ^ 3 + (X * catGF) ^ 2 + (2 - X) * (X * catGF) + (2 - 2 * X)) * X_mul_C_sq

lemma coeff_four_mul (m : ℕ) (f : PowerSeries ℤ) : coeff m (4 * f) = 4 * coeff m f := by
  rw [show (4 : PowerSeries ℤ) = PowerSeries.C (4 : ℤ) from rfl, coeff_C_mul]

lemma coeff_two_mul (m : ℕ) (f : PowerSeries ℤ) : coeff m (2 * f) = 2 * coeff m f := by
  rw [show (2 : PowerSeries ℤ) = PowerSeries.C (2 : ℤ) from rfl, coeff_C_mul]

lemma a_eq (n : ℕ) :
    a n = 2 * (catalan (n + 2) : ℤ) - 4 * catalan (n + 1) + catalan n := by
  have h := congrArg (coeff (n + 3)) X_pow_three_mul
  rw [coeff_X_pow_mul', if_pos (by omega), show n + 3 - 3 = n by omega] at h
  rw [a, h]
  simp only [map_add, map_sub, coeff_four_mul, coeff_two_mul]
  rw [show n + 3 = n + 2 + 1 from rfl, coeff_succ_X_mul, coeff_succ_X_mul,
    show n + 2 = n + 1 + 1 from rfl, coeff_succ_X_mul, show n + 1 = n + 1 from rfl,
    coeff_succ_X_mul]
  simp [catGF, coeff_X, coeff_X_pow]
  ring

lemma cat_rec (k : ℕ) : ((k : ℚ) + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  have h4 : ((k + 1 : ℕ) : ℚ) * ((k + 1 + 1 : ℕ) * catalan (k + 1)) =
      ((k + 1 : ℕ) : ℚ) * (2 * (2 * k + 1) * catalan k) := by
    have : (k + 1) * ((k + 1 + 1) * catalan (k + 1)) =
        (k + 1) * (2 * (2 * k + 1) * catalan k) := by
      rw [h1, h3, ← h2]; ring
    exact_mod_cast this
  have hk : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have := mul_left_cancel₀ hk h4
  push_cast at this
  linarith

lemma cat_succ (k : ℕ) :
    (catalan (k + 1) : ℚ) = 2 * (2 * k + 1) * catalan k / (k + 2) := by
  rw [eq_div_iff (by positivity)]
  linarith [cat_rec k]

end OMA.P_oeis_a071722

theorem OMA.solution : type_of% @OMA.S_oeis_a071722.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  simp only [OMA.P_oeis_a071722.a_eq]
  have key : 2 * (((m + 3 : ℕ) : ℚ) + 3) *
        (2 * (catalan (m + 3 + 2) : ℚ) - 4 * catalan (m + 3 + 1) + catalan (m + 3)) +
      4 * (-3 * ((m + 3 : ℕ) : ℚ) - 4) *
        (2 * (catalan (m + 2 + 2) : ℚ) - 4 * catalan (m + 2 + 1) + catalan (m + 2)) +
      (17 * ((m + 3 : ℕ) : ℚ) - 9) *
        (2 * (catalan (m + 1 + 2) : ℚ) - 4 * catalan (m + 1 + 1) + catalan (m + 1)) +
      2 * (-2 * ((m + 3 : ℕ) : ℚ) + 5) *
        (2 * (catalan (m + 2) : ℚ) - 4 * catalan (m + 1) + catalan m) = 0 := by
    rw [show m + 3 + 2 = m + 4 + 1 by omega, show m + 3 + 1 = m + 3 + 1 from rfl,
      show m + 2 + 2 = m + 3 + 1 by omega, show m + 2 + 1 = m + 2 + 1 from rfl,
      show m + 1 + 2 = m + 2 + 1 by omega, show m + 1 + 1 = m + 1 + 1 from rfl]
    rw [OMA.P_oeis_a071722.cat_succ (m + 4), OMA.P_oeis_a071722.cat_succ (m + 3),
      OMA.P_oeis_a071722.cat_succ (m + 2), OMA.P_oeis_a071722.cat_succ (m + 1),
      OMA.P_oeis_a071722.cat_succ m]
    push_cast
    field_simp
    ring
  exact_mod_cast key
