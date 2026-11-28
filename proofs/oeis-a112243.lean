import OMAStatements.S_oeis_a112243
import Mathlib

namespace OMA.S_oeis_a112243

open PowerSeries

theorem f_const : constantCoeff f = 0 := by
  simp [f]

theorem hsub : HasSubst f := HasSubst.of_constantCoeff_zero' f_const

theorem w_ne : constantCoeff (1 - 2 * X : ℚ⟦X⟧) ≠ 0 := by simp

theorem dE : d⁄dX ℚ E = E * d⁄dX ℚ f := by
  rw [E, derivative_subst hsub, derivative_exp]

theorem df_mul : (1 - 2 * X : ℚ⟦X⟧) ^ 2 * d⁄dX ℚ f = 1 + 2 * X - 2 * X ^ 2 := by
  have hw : (1 - 2 * X : ℚ⟦X⟧) * (1 - 2 * X)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ w_ne
  have hd : d⁄dX ℚ f = (1 + 2 * X) * (1 - 2 * X)⁻¹ +
      (X + X ^ 2) * (2 * ((1 - 2 * X)⁻¹) ^ 2) := by
    rw [f, Derivation.leibniz, derivative_inv']
    have h2 : d⁄dX ℚ (2 * X : ℚ⟦X⟧) = 2 := by
      rw [show (2 * X : ℚ⟦X⟧) = X + X by ring, map_add, derivative_X]
      norm_num
    have hX2 : d⁄dX ℚ ((X : ℚ⟦X⟧) ^ 2) = 2 * X := by
      rw [Derivation.leibniz_pow]
      simp [smul_eq_mul]
    simp only [map_add, map_sub, derivative_X, smul_eq_mul, Derivation.map_one_eq_zero, h2, hX2]
    ring
  rw [hd]
  linear_combination ((1 + 2 * X) * (1 - 2 * X) +
    2 * (X + X ^ 2) * ((1 - 2 * X) * (1 - 2 * X)⁻¹ + 1)) * hw

theorem ode : (1 - 2 * X : ℚ⟦X⟧) ^ 2 * d⁄dX ℚ E = (1 + 2 * X - 2 * X ^ 2) * E := by
  linear_combination E * df_mul + (1 - 2 * X : ℚ⟦X⟧) ^ 2 * dE

theorem coeff_rec (k : ℕ) :
    coeff (k + 3) E * (k + 3) - 4 * (coeff (k + 2) E * (k + 2)) + 4 * (coeff (k + 1) E * (k + 1)) =
      coeff (k + 2) E + 2 * coeff (k + 1) E - 2 * coeff k E := by
  have h := congrArg (coeff (k + 2)) ode
  have hL : (1 - 2 * X : ℚ⟦X⟧) ^ 2 * d⁄dX ℚ E =
      d⁄dX ℚ E - C 4 * (d⁄dX ℚ E * X ^ 1) + C 4 * (d⁄dX ℚ E * X ^ 2) := by
    simp only [map_ofNat]; ring
  have hR : (1 + 2 * X - 2 * X ^ 2 : ℚ⟦X⟧) * E = E + C 2 * (E * X ^ 1) - C 2 * (E * X ^ 2) := by
    simp only [map_ofNat]; ring
  rw [hL, hR] at h
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_derivative,
    if_pos (show 1 ≤ k + 2 by omega), if_pos (show 2 ≤ k + 2 by omega),
    show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega] at h
  push_cast at h
  linear_combination h

end OMA.S_oeis_a112243

open OMA.S_oeis_a112243 in
theorem OMA.solution : type_of% @OMA.S_oeis_a112243.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [a, show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega, Nat.factorial_succ]
  push_cast
  have h := coeff_rec k
  linear_combination ((k.factorial : ℚ) * (k + 1) * (k + 2)) * h
