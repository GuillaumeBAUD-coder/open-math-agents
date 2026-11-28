import OMAStatements.S_oeis_a227081
import Mathlib

/-!
Credit: @ivillar
Proof: S is (1 + x)^(1/2) composed with R - 1, so S^2 = R = (1 - 2x)(1 - 6x), and
R (2 S') = R' S. Let H be the g.f. and V = (3 - 2x) H - 1. Since
3 - 20x + 12x^2 = (1 - 6x)(3 - 2x), we get V (1 - 6x) = 2S. Differentiating this and using the
equation for S' gives (1 - 6x) (2 R V' - 4 V) = 0, so R V' = 2V, i.e.
(k + 1) v(k + 1) - (8k + 2) v(k) + 12 (k - 1) v(k - 1) = 0 for v(k) = [x^k] V. Since
v(k) = 3 a(k) - 2 a(k - 1) for k >= 1, substituting gives twice the conjectured recurrence.
-/

namespace OMAA227081Helpers
open OMA.S_oeis_a227081 PowerSeries

theorem hSR : S ^ 2 = R := by
  have hR : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow hR, sq, ← binomialSeries_add,
    show (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) by norm_num, binomialSeries_nat, pow_one,
    ← coe_substAlgHom hR, map_add, map_one, coe_substAlgHom hR, subst_X hR]
  ring

noncomputable def H : ℚ⟦X⟧ := (1 - 6 * X + (2) * S) * (3 - 20 * X + 12 * X ^ 2 : PowerSeries ℚ)⁻¹

noncomputable def V : ℚ⟦X⟧ := H * (3 - 2 * X) - 1

theorem hH : H * (3 - 20 * X + 12 * X ^ 2) = 1 - 6 * X + 2 * S := by
  have hne : constantCoeff (3 - 20 * X + 12 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    rw [show (3 - 20 * X + 12 * X ^ 2 : ℚ⟦X⟧) = C 3 - C 20 * X + C 12 * X ^ 2 by
      rw [map_ofNat C 3, map_ofNat C 20, map_ofNat C 12], map_add, map_sub, constantCoeff_C,
      map_mul, map_mul, constantCoeff_X, map_pow, constantCoeff_X]
    norm_num
  unfold H
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hne, mul_one]

theorem hV : V * (1 - 6 * X) = 2 * S := by
  unfold V
  linear_combination hH

theorem dS : (1 - 8 * X + 12 * X ^ 2) * (2 * d⁄dX ℚ S) = (-8 + 24 * X) * S := by
  have h1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
    rw [derivative_pow]; norm_num
  have h2 : d⁄dX ℚ (1 - C 8 * X + C 12 * X ^ 2 : ℚ⟦X⟧) = -(C 8) + C 24 * X := by
    ext k
    rw [coeff_derivative]
    rcases k with _ | _ | k <;> simp [coeff_X_pow, coeff_one, coeff_C]
    norm_num
  rw [map_ofNat C 8, map_ofNat C 12, map_ofNat C 24] at h2
  have hS2 : S ^ 2 = 1 - 8 * X + 12 * X ^ 2 := by rw [hSR, R]
  rw [show (-8 + 24 * X : ℚ⟦X⟧) = -(8 : ℚ⟦X⟧) + 24 * X by ring, ← h2, ← hS2, h1]
  ring

theorem ode : 2 * ((1 - 8 * X + 12 * X ^ 2) * d⁄dX ℚ V) - 4 * V = 0 := by
  have h3 : d⁄dX ℚ (1 - C 6 * X : ℚ⟦X⟧) = -(C 6) := by
    ext k
    rw [coeff_derivative]
    rcases k with _ | k <;> simp [coeff_one, coeff_C]
  have hd2 : d⁄dX ℚ (C 2 * S) = C 2 * d⁄dX ℚ S := by
    rw [Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul]
  have hV' : V * (1 - C 6 * X) = C 2 * S := by
    rw [map_ofNat C 6, map_ofNat C 2]
    exact hV
  have hd := congrArg (d⁄dX ℚ) hV'
  rw [Derivation.leibniz, h3, hd2, smul_eq_mul, smul_eq_mul] at hd
  rw [map_ofNat C 6, map_ofNat C 2] at hd
  have hq : (1 - 6 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp at this
  have key : (1 - 6 * X) * (2 * ((1 - 8 * X + 12 * X ^ 2) * d⁄dX ℚ V) - 4 * V) = 0 := by
    linear_combination (2 * (1 - 8 * X + 12 * X ^ 2)) * hd + 2 * dS - (-8 + 24 * X) * hV
  exact (mul_eq_zero.mp key).resolve_left hq

theorem T (j i1 i2 i3 : ℕ) (h1 : i1 = j + 1) (h2 : i2 = j + 1 + 1) (h3 : i3 = j + 1 + 1 + 1) :
    2 * ((j : ℚ) + 3) * coeff i3 V - 16 * ((j : ℚ) + 2) * coeff i2 V
      + 24 * ((j : ℚ) + 1) * coeff i1 V - 4 * coeff i2 V = 0 := by
  subst h1 h2 h3
  have o := ode
  rw [← map_ofNat C 2, ← map_ofNat C 8, ← map_ofNat C 12, ← map_ofNat C 4] at o
  have e : C 2 * ((1 - C 8 * X + C 12 * X ^ 2) * d⁄dX ℚ V) - C 4 * V =
      C 2 * d⁄dX ℚ V - C 2 * (C 8 * (X * d⁄dX ℚ V))
        + C 2 * (C 12 * (X * (X * d⁄dX ℚ V))) - C 4 * V := by ring
  rw [e] at o
  have h := congrArg (coeff (j + 1 + 1)) o
  simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_derivative, map_zero] at h
  push_cast at h
  linear_combination h

theorem hv (k i : ℕ) (hi : i = k + 1) : coeff i V = 3 * a i - 2 * a k := by
  subst hi
  have e : V = C 3 * H - C 2 * (X * H) - 1 := by
    unfold V
    rw [map_ofNat C 3, map_ofNat C 2]
    ring
  rw [e, map_sub, map_sub, coeff_C_mul, coeff_C_mul, coeff_succ_X_mul, coeff_one,
    if_neg (by omega), show a (k + 1) = coeff (k + 1) H from rfl, show a k = coeff k H from rfl]
  ring

end OMAA227081Helpers

open OMAA227081Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a227081.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  push_cast
  have t := T m (m + 1) (m + 2) (m + 3) (by omega) (by omega) (by omega)
  have g3 := hv (m + 2) (m + 3) (by omega)
  have g2 := hv (m + 1) (m + 2) (by omega)
  have g1 := hv m (m + 1) (by omega)
  linear_combination (1 / 2 : ℚ) * t - ((m : ℚ) + 3) * g3 + (8 * (m : ℚ) + 18) * g2
    - (12 * ((m : ℚ) + 1)) * g1
