import OMAStatements.S_oeis_a173993
import Mathlib

open OMA.S_oeis_a173993
open PowerSeries

namespace Pa173993

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem sq_step (S E : PowerSeries ℚ) (h : S ^ 2 = E) : 2 * E * d⁄dX ℚ S = d⁄dX ℚ E * S := by
  have h1 := congrArg (d⁄dX ℚ) h
  simp only [pow_two, Derivation.leibniz, smul_eq_mul] at h1
  linear_combination (-2 * d⁄dX ℚ S) * h + S * h1

theorem th_step (P B U V S : PowerSeries ℚ) (h : P * B = U + V * S) :
    d⁄dX ℚ P * B + P * d⁄dX ℚ B = d⁄dX ℚ U + d⁄dX ℚ V * S + V * d⁄dX ℚ S := by
  have h1 := congrArg (d⁄dX ℚ) h
  simp only [Derivation.leibniz, map_add, smul_eq_mul] at h1
  linear_combination h1

theorem ne_of_coeff (p : PowerSeries ℚ) (m : ℕ) (h : coeff m p ≠ 0) : p ≠ 0 := by
  intro h0; rw [h0, map_zero] at h; exact h rfl

set_option maxHeartbeats 2000000 in
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 4 * X + 12 * X ^ 3 - 8 * X ^ 4)
    (hL : (2 - 8 * X + 6 * X ^ 2) * A = (-1 + 4 * X - 2 * X ^ 2) + (1) * S) :
    (-2 * X + 14 * X ^ 2 - 36 * X ^ 3 + 40 * X ^ 4 - 14 * X ^ 5) * (A) + (1 - 8 * X + 19 * X ^ 2 - 56 * X ^ 4 + 68 * X ^ 5 - 24 * X ^ 6) * (X * d⁄dX ℚ A) = X - 6 * X ^ 2 + 15 * X ^ 3 - 20 * X ^ 4 + 10 * X ^ 5 := by
  have hdD : d⁄dX ℚ (1 - 4 * X + 12 * X ^ 3 - 8 * X ^ 4 : PowerSeries ℚ) = -4 + 36 * X ^ 2 - 32 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (2 - 8 * X + 6 * X ^ 2 : PowerSeries ℚ) = -8 + 12 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (-1 + 4 * X - 2 * X ^ 2 : PowerSeries ℚ) = 4 - 4 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (1 : PowerSeries ℚ) = 0 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (1 - 12 * X + 54 * X ^ 2 - 100 * X ^ 3 + X ^ 4 + 292 * X ^ 5 - 464 * X ^ 6 + 300 * X ^ 7 - 72 * X ^ 8) * (X * d⁄dX ℚ A) = (X ^ 2 - 6 * X ^ 3 + 8 * X ^ 4 + 12 * X ^ 5 - 32 * X ^ 6 + 16 * X ^ 7) + (X - 7 * X ^ 2 + 18 * X ^ 3 - 20 * X ^ 4 + 7 * X ^ 5) * S := by
    have hg : (4 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 16 * X ^ 2 + 38 * X ^ 3 - 112 * X ^ 5 + 136 * X ^ 6 - 48 * X ^ 7) * E1 + (8 * X - 44 * X ^ 2 + 48 * X ^ 3 + 96 * X ^ 4 - 208 * X ^ 5 + 96 * X ^ 6) * L0 + (X - 4 * X ^ 2 + 3 * X ^ 3) * hS1
  have key : (2 - 24 * X + 108 * X ^ 2 - 200 * X ^ 3 + 2 * X ^ 4 + 584 * X ^ 5 - 928 * X ^ 6 + 600 * X ^ 7 - 144 * X ^ 8) * (((-2 * X + 14 * X ^ 2 - 36 * X ^ 3 + 40 * X ^ 4 - 14 * X ^ 5) * (A) + (1 - 8 * X + 19 * X ^ 2 - 56 * X ^ 4 + 68 * X ^ 5 - 24 * X ^ 6) * (X * d⁄dX ℚ A)) - (X - 6 * X ^ 2 + 15 * X ^ 3 - 20 * X ^ 4 + 10 * X ^ 5)) = 0 := by
    linear_combination (-2 * X + 30 * X ^ 2 - 186 * X ^ 3 + 594 * X ^ 4 - 906 * X ^ 5 - 48 * X ^ 6 + 2750 * X ^ 7 - 5024 * X ^ 8 + 4368 * X ^ 9 - 1912 * X ^ 10 + 336 * X ^ 11) * L0 + (2 - 16 * X + 38 * X ^ 2 - 112 * X ^ 4 + 136 * X ^ 5 - 48 * X ^ 6) * L1
  have hne : (2 - 24 * X + 108 * X ^ 2 - 200 * X ^ 3 + 2 * X ^ 4 + 584 * X ^ 5 - 928 * X ^ 6 + 600 * X ^ 7 - 144 * X ^ 8 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

theorem S_sq : S ^ 2 = 1 - 4 * X + 12 * X ^ 3 - 8 * X ^ 4 := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow h0, hB, ← coe_substAlgHom h0, map_add, map_one,
    coe_substAlgHom, subst_X h0, R]
  ring

theorem gf_eq : (2 - 8 * X + 6 * X ^ 2) * ((-1 + 4 * X - 2 * X ^ 2 + S) * (2 - 8 * X + 6 * X ^ 2 : PowerSeries ℚ)⁻¹) = -1 + 4 * X - 2 * X ^ 2 + S := by
  have hd : constantCoeff (2 - 8 * X + 6 * X ^ 2 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 - 8 * X + 6 * X ^ 2 : PowerSeries ℚ) hd
  linear_combination (-1 + 4 * X - 2 * X ^ 2 + S) * hinv

end Pa173993

theorem OMA.solution : type_of% @OMA.S_oeis_a173993.main := by
  intro n hn
  have hL := Pa173993.gf_eq
  have ha : ∀ m, a m = coeff (m + 1) ((-1 + 4 * X - 2 * X ^ 2 + S) * (2 - 8 * X + 6 * X ^ 2 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((-1 + 4 * X - 2 * X ^ 2 + S) * (2 - 8 * X + 6 * X ^ 2 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (2 - 8 * X + 6 * X ^ 2) * A = (-1 + 4 * X - 2 * X ^ 2) + (1) * S := by
    linear_combination hL
  have e := congrArg (coeff (n + 1)) (Pa173993.ode S A Pa173993.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  simp only [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega, show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega, show k + 6 - 5 = k + 1 by omega, show k + 6 - 6 = k by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa173993.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa173993.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
