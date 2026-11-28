import OMAStatements.S_oeis_a099363
import Mathlib

open OMA.S_oeis_a099363
open PowerSeries

namespace Pa099363

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem two_ne : (2 : PowerSeries ℚ) ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  rw [map_ofNat, map_zero] at this
  norm_num at this

noncomputable def cat : PowerSeries ℚ := map (Nat.castRingHom ℚ) catalanSeries

theorem cat_eq : cat ^ 2 * X + 1 = cat := by
  have := congrArg (map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
  simpa [cat] using this

theorem catalan_subst (u : PowerSeries ℚ) (hu : constantCoeff u = 0) :
    (catalanSeries.map (Nat.castRingHom ℚ)).subst u ^ 2 * u + 1 =
      (catalanSeries.map (Nat.castRingHom ℚ)).subst u := by
  have ha := HasSubst.of_constantCoeff_zero' hu
  have hc := congrArg (substAlgHom ha) cat_eq
  rw [map_add, map_mul, map_pow, map_one, substAlgHom_X, coe_substAlgHom] at hc
  exact hc

noncomputable def A : PowerSeries ℚ := PowerSeries.mk a

theorem hcat : c2 ^ 2 * X ^ 2 + 1 = c2 := by
  unfold c2
  exact catalan_subst _ (by simp)

theorem hXA : X * A = 1 - (1 - X) * c2 := by
  have h0 : constantCoeff c2 = 1 := by
    have := congrArg constantCoeff hcat
    simp only [map_add, map_mul, map_pow, constantCoeff_X, map_one] at this
    simpa using this.symm
  ext n
  rcases n with _ | n
  · simp [h0]
  · rw [coeff_succ_X_mul, A, coeff_mk, a]

theorem quad : (X ^ 3) * A ^ 2 + (1 - X - 2 * X ^ 2) * A + (-1 + 2 * X) = 0 := by
  have h : X * ((X ^ 3) * A ^ 2 + (1 - X - 2 * X ^ 2) * A + (-1 + 2 * X)) = 0 := by
    linear_combination (X ^ 2 * (X * A + (1 - (1 - X) * c2)) + (1 - X - 2 * X ^ 2)) * hXA +
      (1 - X) ^ 2 * hcat
  exact (mul_eq_zero.mp h).resolve_left X_ne_zero

theorem ode : (X - X ^ 2 - 4 * X ^ 3 + 4 * X ^ 4) * d⁄dX ℚ A + (3 - 2 * X - 8 * X ^ 2 + 4 * X ^ 3) * A = 3 - 6 * X := by
  set S : PowerSeries ℚ := 2 * (X ^ 3) * A + (1 - X - 2 * X ^ 2) with hSdef
  have hS : S ^ 2 = (1 - X - 2 * X ^ 2) ^ 2 - 4 * (X ^ 3) * (-1 + 2 * X) := by
    rw [hSdef]; linear_combination (4 * (X ^ 3)) * quad
  have hA : 2 * (X ^ 3) * A = -(1 - X - 2 * X ^ 2) + S := by rw [hSdef]; ring
  have hdD : d⁄dX ℚ ((1 - X - 2 * X ^ 2) ^ 2 - 4 * (X ^ 3) * (-1 + 2 * X)) = -2 - 6 * X + 24 * X ^ 2 - 16 * X ^ 3 := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have hda : d⁄dX ℚ (2 * (X ^ 3)) = 6 * X ^ 2 := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have hdb : d⁄dX ℚ (1 - X - 2 * X ^ 2) = -1 - 4 * X := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have h1 : 2 * S * d⁄dX ℚ S = -2 - 6 * X + 24 * X ^ 2 - 16 * X ^ 3 := by
    have := congrArg (d⁄dX ℚ) hS
    rw [derivative_pow, hdD] at this
    rw [← this]; push_cast; ring
  have E1 : (6 * X ^ 2) * A + 2 * (X ^ 3) * d⁄dX ℚ A = -(-1 - 4 * X) + d⁄dX ℚ S := by
    have := congrArg (d⁄dX ℚ) hA
    rw [Derivation.leibniz, map_add, map_neg, hda, hdb, smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  have E2 : 2 * ((1 - X - 2 * X ^ 2) ^ 2 - 4 * (X ^ 3) * (-1 + 2 * X)) * d⁄dX ℚ S = (-2 - 6 * X + 24 * X ^ 2 - 16 * X ^ 3) * S := by
    linear_combination (-2 * d⁄dX ℚ S) * hS + S * h1
  have key : (2 * ((1 - X - 2 * X ^ 2) ^ 2 - 4 * (X ^ 3) * (-1 + 2 * X)) * (2 * (X ^ 3))) *
      ((X - X ^ 2 - 4 * X ^ 3 + 4 * X ^ 4) * d⁄dX ℚ A + (3 - 2 * X - 8 * X ^ 2 + 4 * X ^ 3) * A - (3 - 6 * X)) = 0 := by
    linear_combination (2 * ((1 - X - 2 * X ^ 2) ^ 2 - 4 * (X ^ 3) * (-1 + 2 * X)) * (X - X ^ 2 - 4 * X ^ 3 + 4 * X ^ 4)) * E1 +
      (X - X ^ 2 - 4 * X ^ 3 + 4 * X ^ 4) * E2 - ((X - X ^ 2 - 4 * X ^ 3 + 4 * X ^ 4) * (-2 - 6 * X + 24 * X ^ 2 - 16 * X ^ 3)) * hA
  have hne : ((2 : PowerSeries ℚ) * ((1 - X - 2 * X ^ 2) ^ 2 - 4 * (X ^ 3) * (-1 + 2 * X)) * (2 * (X ^ 3))) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne ?_) (mul_ne_zero two_ne (pow_ne_zero 3 X_ne_zero))
    intro h0
    have := congrArg constantCoeff h0
    simp only [map_ofNat, map_mul, map_sub, map_add, map_neg, map_pow, constantCoeff_X,
      constantCoeff_one, map_one, map_zero] at this
    norm_num at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

end Pa099363

theorem OMA.solution : type_of% @OMA.S_oeis_a099363.main := by
  intro n hn
  have e := congrArg (coeff n) Pa099363.ode
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega]
  simp only [Pa099363.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa099363.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X,
    coeff_one] at e
  simp at e
  simp only [Pa099363.A, coeff_mk] at e
  push_cast at e ⊢
  linarith
