import OMAStatements.S_oeis_a108630

-- Disproof. The argument follows the accepted proof of the template entry OEIS A108629:
-- R = rootSeries satisfies R^2 = 1 + t, so 2 (1 + t) R' = t' R; substituting
-- R = 1 + X - 2 (1 + X + X^2) A gives a first-order linear ODE for A. Its coefficients of
-- X^0, ..., X^6, together with a(0) = 0, pin down a(1..7) = 1, 1, 2, 6, 17, 54, 178, and the
-- conjectured recurrence at n = 7 would need 6 * 178 = 1068 to equal 900.
-- (The recurrence does hold for the index-shifted sequence b(n) = a(n-1).)

namespace OMA.P_a108630
open OMA.S_oeis_a108630 PowerSeries

lemma hasSubst_t : HasSubst radicandTail :=
  HasSubst.of_constantCoeff_zero' (by simp [radicandTail])

lemma root_sq : rootSeries ^ 2 = 1 + radicandTail := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  unfold rootSeries
  rw [← subst_pow hasSubst_t, hB, ← coe_substAlgHom hasSubst_t, map_add, map_one,
    coe_substAlgHom, subst_X hasSubst_t]

lemma d_t : d⁄dX ℚ radicandTail = -2 - 14 * X - 24 * X ^ 2 - 16 * X ^ 3 := by
  have : radicandTail = C (-2 : ℚ) * X + C (-7 : ℚ) * X ^ 2 + C (-8 : ℚ) * X ^ 3
      + C (-4 : ℚ) * X ^ 4 := by
    simp only [radicandTail, map_neg, map_ofNat]; ring
  rw [this]
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, derivative_C, derivative_X,
    smul_eq_mul]
  simp only [map_neg, map_ofNat]
  ring

lemma two_D_A : 2 * (1 + X + X ^ 2) * series = 1 + X - rootSeries := by
  unfold series
  have h : constantCoeff (2 * (1 + X + X ^ 2) : PowerSeries ℚ) ≠ 0 := by
    rw [map_mul, map_ofNat]; simp
  rw [mul_comm, mul_assoc, mul_comm _ (2 * (1 + X + X ^ 2)), PowerSeries.mul_inv_cancel _ h,
    mul_one]

lemma ode :
    (-4 + 4 * X + 32 * X ^ 2 + 68 * X ^ 3 + 76 * X ^ 4 + 48 * X ^ 5 + 16 * X ^ 6)
        * d⁄dX ℚ series
      + (-8 - 32 * X - 36 * X ^ 2 - 20 * X ^ 3) * series
      + (4 + 12 * X + 24 * X ^ 2 + 24 * X ^ 3 + 8 * X ^ 4) = 0 := by
  have hR : rootSeries = 1 + X - 2 * (1 + X + X ^ 2) * series := by rw [two_D_A]; ring
  have h2 := congrArg (d⁄dX ℚ) root_sq
  rw [sq, Derivation.leibniz, map_add, derivative_one, d_t, smul_eq_mul,
    zero_add] at h2
  have h3 : 2 * (1 + radicandTail) * d⁄dX ℚ rootSeries
      = rootSeries * (-2 - 14 * X - 24 * X ^ 2 - 16 * X ^ 3) := by
    rw [← root_sq]; linear_combination rootSeries * h2
  have hdR := congrArg (d⁄dX ℚ) hR
  simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, derivative_one,
    derivative_X, smul_eq_mul] at hdR
  have h2d : d⁄dX ℚ (2 : PowerSeries ℚ) = 0 := by
    rw [show (2 : PowerSeries ℚ) = C 2 by simp only [map_ofNat], derivative_C]
  rw [h2d] at hdR
  simp only [radicandTail] at h3
  linear_combination h3 - 2 * (1 + (-2 * X - 7 * X ^ 2 - 8 * X ^ 3 - 4 * X ^ 4)) * hdR
    + (-2 - 14 * X - 24 * X ^ 2 - 16 * X ^ 3) * hR

lemma ode' :
    C (-4 : ℚ) * X ^ 0 * d⁄dX ℚ series + C (4 : ℚ) * X ^ 1 * d⁄dX ℚ series
      + C (32 : ℚ) * X ^ 2 * d⁄dX ℚ series + C (68 : ℚ) * X ^ 3 * d⁄dX ℚ series
      + C (76 : ℚ) * X ^ 4 * d⁄dX ℚ series + C (48 : ℚ) * X ^ 5 * d⁄dX ℚ series
      + C (16 : ℚ) * X ^ 6 * d⁄dX ℚ series
      + C (-8 : ℚ) * X ^ 0 * series + C (-32 : ℚ) * X ^ 1 * series
      + C (-36 : ℚ) * X ^ 2 * series + C (-20 : ℚ) * X ^ 3 * series
      + (C (4 : ℚ) * X ^ 0 + C (12 : ℚ) * X ^ 1 + C (24 : ℚ) * X ^ 2 + C (24 : ℚ) * X ^ 3
        + C (8 : ℚ) * X ^ 4) = 0 := by
  simp only [map_neg, map_ofNat]
  linear_combination ode

/-- The coefficient of `x^m` in the differential equation. -/
lemma coeff_eq (m : ℕ) :
    PowerSeries.coeff m (C (-4 : ℚ) * X ^ 0 * d⁄dX ℚ series + C (4 : ℚ) * X ^ 1 * d⁄dX ℚ series
      + C (32 : ℚ) * X ^ 2 * d⁄dX ℚ series + C (68 : ℚ) * X ^ 3 * d⁄dX ℚ series
      + C (76 : ℚ) * X ^ 4 * d⁄dX ℚ series + C (48 : ℚ) * X ^ 5 * d⁄dX ℚ series
      + C (16 : ℚ) * X ^ 6 * d⁄dX ℚ series
      + C (-8 : ℚ) * X ^ 0 * series + C (-32 : ℚ) * X ^ 1 * series
      + C (-36 : ℚ) * X ^ 2 * series + C (-20 : ℚ) * X ^ 3 * series
      + (C (4 : ℚ) * X ^ 0 + C (12 : ℚ) * X ^ 1 + C (24 : ℚ) * X ^ 2 + C (24 : ℚ) * X ^ 3
        + C (8 : ℚ) * X ^ 4)) = 0 := by
  rw [ode']; simp

lemma root_const : constantCoeff rootSeries = 1 := by
  have h0 : constantCoeff radicandTail = 0 := by simp [radicandTail]
  have hB : constantCoeff (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - 1) = 0 := by
    simp [binomialSeries_constantCoeff]
  have h := constantCoeff_subst_eq_zero (S := ℚ) h0 _ hB
  rw [← coe_substAlgHom hasSubst_t, map_sub, map_one, coe_substAlgHom] at h
  have h' : constantCoeff rootSeries - 1 = 0 := by
    unfold rootSeries
    exact h
  linear_combination h'

lemma a_zero : a 0 = 0 := by
  have h0 := congrArg constantCoeff two_D_A
  have hr := root_const
  simp only [map_mul, map_add, map_sub, map_one, map_ofNat, constantCoeff_X, map_pow] at h0
  unfold a
  rw [coeff_zero_eq_constantCoeff_apply]
  rw [hr] at h0
  linear_combination h0 / 2

end OMA.P_a108630

open OMA.S_oeis_a108630 OMA.P_a108630 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a108630.main) := by
  intro H
  have hz := a_zero
  unfold a at hz
  rw [coeff_zero_eq_constantCoeff_apply] at hz
  have h0 := coeff_eq 0
  have h1 := coeff_eq 1
  have h2 := coeff_eq 2
  have h3 := coeff_eq 3
  have h4 := coeff_eq 4
  have h5 := coeff_eq 5
  have h6 := coeff_eq 6
  simp only [mul_assoc, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_derivative,
    coeff_X_pow] at h0 h1 h2 h3 h4 h5 h6
  norm_num at h0 h1 h2 h3 h4 h5 h6
  have h7 := H 7 le_rfl
  norm_num [a] at h7
  rw [hz] at h0 h1 h2 h3
  linarith
