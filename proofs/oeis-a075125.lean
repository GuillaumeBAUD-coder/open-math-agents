import OMAStatements.S_oeis_a075125
import Mathlib

open OMA.S_oeis_a075125
open PowerSeries

namespace Pa075125

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
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hL : (2) * A = (X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6) + (-X ^ 2 - X ^ 3 + X ^ 4) * S) :
    (198 - 288 * X - 156 * X ^ 2 - 42 * X ^ 3 - 6 * X ^ 4) * (A) + (-179 + 280 * X + 125 * X ^ 2 + 112 * X ^ 3 + X ^ 4) * (X * d⁄dX ℚ A) + (48 - 84 * X - 36 * X ^ 2 - 60 * X ^ 3 + 24 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (-4 + 8 * X + 4 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = -6 * X ^ 4 := by
  have hdD : d⁄dX ℚ (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 : PowerSeries ℚ) = -2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (2 : PowerSeries ℚ) = 0 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6 : PowerSeries ℚ) = 2 * X - 4 * X ^ 3 - 10 * X ^ 4 + 6 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-X ^ 2 - X ^ 3 + X ^ 4 : PowerSeries ℚ) = -2 * X - 3 * X ^ 2 + 4 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * (X * d⁄dX ℚ A) = (X ^ 2 - 2 * X ^ 3 - 3 * X ^ 4 - 3 * X ^ 5 + 16 * X ^ 6 + 3 * X ^ 7 + 5 * X ^ 8 - 11 * X ^ 9 + 3 * X ^ 10) + (-X ^ 2 + X ^ 3 + 7 * X ^ 4 + X ^ 5 - 8 * X ^ 7 + 3 * X ^ 8) * S := by
    have hg : (4 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 4 * X ^ 2 - 2 * X ^ 3 - 4 * X ^ 4 + 2 * X ^ 5) * E1 + (0) * L0 + (-X ^ 3 - X ^ 4 + X ^ 5) * hS1
  have dP2 : d⁄dX ℚ (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 : PowerSeries ℚ) = -2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (X ^ 2 - 2 * X ^ 3 - 3 * X ^ 4 - 3 * X ^ 5 + 16 * X ^ 6 + 3 * X ^ 7 + 5 * X ^ 8 - 11 * X ^ 9 + 3 * X ^ 10 : PowerSeries ℚ) = 2 * X - 6 * X ^ 2 - 12 * X ^ 3 - 15 * X ^ 4 + 96 * X ^ 5 + 21 * X ^ 6 + 40 * X ^ 7 - 99 * X ^ 8 + 30 * X ^ 9 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (-X ^ 2 + X ^ 3 + 7 * X ^ 4 + X ^ 5 - 8 * X ^ 7 + 3 * X ^ 8 : PowerSeries ℚ) = -2 * X + 3 * X ^ 2 + 28 * X ^ 3 + 5 * X ^ 4 - 56 * X ^ 6 + 24 * X ^ 7 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (1 - 4 * X + 2 * X ^ 2 + 11 * X ^ 4 + 2 * X ^ 6 - 4 * X ^ 7 + X ^ 8) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (2 * X ^ 2 - 8 * X ^ 3 - 4 * X ^ 4 + 7 * X ^ 5 + 124 * X ^ 6 - 122 * X ^ 7 - 48 * X ^ 8 - 283 * X ^ 9 + 184 * X ^ 10 - 18 * X ^ 11 + 128 * X ^ 12 - 97 * X ^ 13 + 18 * X ^ 14) + (-2 * X ^ 2 + 6 * X ^ 3 + 24 * X ^ 4 - 45 * X ^ 5 - 33 * X ^ 6 - 94 * X ^ 7 + 135 * X ^ 8 + 6 * X ^ 9 + 67 * X ^ 10 - 79 * X ^ 11 + 18 * X ^ 12) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 4 * X ^ 2 - 2 * X ^ 3 - 4 * X ^ 4 + 2 * X ^ 5) * E2 + (4 * X + 4 * X ^ 2 + 12 * X ^ 3 - 8 * X ^ 4) * L1 + (-X ^ 3 + X ^ 4 + 7 * X ^ 5 + X ^ 6 - 8 * X ^ 8 + 3 * X ^ 9) * hS1
  have dP3 : d⁄dX ℚ (1 - 4 * X + 2 * X ^ 2 + 11 * X ^ 4 + 2 * X ^ 6 - 4 * X ^ 7 + X ^ 8 : PowerSeries ℚ) = -4 + 4 * X + 44 * X ^ 3 + 12 * X ^ 5 - 28 * X ^ 6 + 8 * X ^ 7 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU3 : d⁄dX ℚ (2 * X ^ 2 - 8 * X ^ 3 - 4 * X ^ 4 + 7 * X ^ 5 + 124 * X ^ 6 - 122 * X ^ 7 - 48 * X ^ 8 - 283 * X ^ 9 + 184 * X ^ 10 - 18 * X ^ 11 + 128 * X ^ 12 - 97 * X ^ 13 + 18 * X ^ 14 : PowerSeries ℚ) = 4 * X - 24 * X ^ 2 - 16 * X ^ 3 + 35 * X ^ 4 + 744 * X ^ 5 - 854 * X ^ 6 - 384 * X ^ 7 - 2547 * X ^ 8 + 1840 * X ^ 9 - 198 * X ^ 10 + 1536 * X ^ 11 - 1261 * X ^ 12 + 252 * X ^ 13 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV3 : d⁄dX ℚ (-2 * X ^ 2 + 6 * X ^ 3 + 24 * X ^ 4 - 45 * X ^ 5 - 33 * X ^ 6 - 94 * X ^ 7 + 135 * X ^ 8 + 6 * X ^ 9 + 67 * X ^ 10 - 79 * X ^ 11 + 18 * X ^ 12 : PowerSeries ℚ) = -4 * X + 18 * X ^ 2 + 96 * X ^ 3 - 225 * X ^ 4 - 198 * X ^ 5 - 658 * X ^ 6 + 1080 * X ^ 7 + 54 * X ^ 8 + 670 * X ^ 9 - 869 * X ^ 10 + 216 * X ^ 11 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E3 := th_step _ _ _ _ _ L2
  simp only [dP3, dU3, dV3] at E3
  have L3 : (1 - 6 * X + 9 * X ^ 2 - 2 * X ^ 3 + 18 * X ^ 4 - 30 * X ^ 5 - 7 * X ^ 6 - 30 * X ^ 7 + 18 * X ^ 8 - 2 * X ^ 9 + 9 * X ^ 10 - 6 * X ^ 11 + X ^ 12) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = (4 * X ^ 2 - 24 * X ^ 3 + 4 * X ^ 4 + 59 * X ^ 5 + 642 * X ^ 6 - 1829 * X ^ 7 + 618 * X ^ 8 - 1626 * X ^ 9 + 5990 * X ^ 10 - 1413 * X ^ 11 + 2454 * X ^ 12 - 5450 * X ^ 13 + 1910 * X ^ 14 - 1149 * X ^ 15 + 1690 * X ^ 16 - 773 * X ^ 17 + 108 * X ^ 18) + (-4 * X ^ 2 + 20 * X ^ 3 + 76 * X ^ 4 - 355 * X ^ 5 + 119 * X ^ 6 - 265 * X ^ 7 + 2210 * X ^ 8 - 1181 * X ^ 9 + 375 * X ^ 10 - 3083 * X ^ 11 + 1464 * X ^ 12 - 465 * X ^ 13 + 1133 * X ^ 14 - 665 * X ^ 15 + 108 * X ^ 16) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 4 * X ^ 2 - 2 * X ^ 3 - 4 * X ^ 4 + 2 * X ^ 5) * E3 + (8 * X + 8 * X ^ 2 + 24 * X ^ 3 - 16 * X ^ 4) * L2 + (-2 * X ^ 3 + 6 * X ^ 4 + 24 * X ^ 5 - 45 * X ^ 6 - 33 * X ^ 7 - 94 * X ^ 8 + 135 * X ^ 9 + 6 * X ^ 10 + 67 * X ^ 11 - 79 * X ^ 12 + 18 * X ^ 13) * hS1
  have key : (2 - 12 * X + 18 * X ^ 2 - 4 * X ^ 3 + 36 * X ^ 4 - 60 * X ^ 5 - 14 * X ^ 6 - 60 * X ^ 7 + 36 * X ^ 8 - 4 * X ^ 9 + 18 * X ^ 10 - 12 * X ^ 11 + 2 * X ^ 12) * (((198 - 288 * X - 156 * X ^ 2 - 42 * X ^ 3 - 6 * X ^ 4) * (A) + (-179 + 280 * X + 125 * X ^ 2 + 112 * X ^ 3 + X ^ 4) * (X * d⁄dX ℚ A) + (48 - 84 * X - 36 * X ^ 2 - 60 * X ^ 3 + 24 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (-4 + 8 * X + 4 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A)))) - (-6 * X ^ 4)) = 0 := by
    linear_combination (198 - 1476 * X + 3354 * X ^ 2 - 2094 * X ^ 3 + 2982 * X ^ 4 - 11154 * X ^ 5 + 4476 * X ^ 6 + 12 * X ^ 7 + 14448 * X ^ 8 - 426 * X ^ 9 + 852 * X ^ 10 - 4044 * X ^ 11 + 498 * X ^ 12 + 282 * X ^ 13 + 42 * X ^ 14 - 6 * X ^ 15 - 6 * X ^ 16) * L0 + (-358 + 1992 * X - 2706 * X ^ 2 + 344 * X ^ 3 - 4332 * X ^ 4 + 6600 * X ^ 5 + 2038 * X ^ 6 + 5016 * X ^ 7 - 2076 * X ^ 8 + 8 * X ^ 9 - 642 * X ^ 10 + 216 * X ^ 11 + 2 * X ^ 12) * L1 + (96 - 360 * X + 168 * X ^ 2 + 792 * X ^ 4 + 120 * X ^ 6 - 216 * X ^ 7 + 48 * X ^ 8) * L2 + (-8 + 16 * X + 8 * X ^ 2 + 16 * X ^ 3 - 8 * X ^ 4) * L3
  have hne : (2 - 12 * X + 18 * X ^ 2 - 4 * X ^ 3 + 36 * X ^ 4 - 60 * X ^ 5 - 14 * X ^ 6 - 60 * X ^ 7 + 36 * X ^ 8 - 4 * X ^ 9 + 18 * X ^ 10 - 12 * X ^ 11 + 2 * X ^ 12 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

theorem S_sq : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow h0, hB, ← coe_substAlgHom h0, map_add, map_one,
    coe_substAlgHom, subst_X h0, R]
  ring

theorem gf_eq : (2) * ((X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6 + (-X ^ 2 - X ^ 3 + X ^ 4) * S) * (2 : PowerSeries ℚ)⁻¹) = X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6 + (-X ^ 2 - X ^ 3 + X ^ 4) * S := by
  have hd : constantCoeff (2 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 : PowerSeries ℚ) hd
  linear_combination (X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6 + (-X ^ 2 - X ^ 3 + X ^ 4) * S) * hinv

end Pa075125

theorem OMA.solution : type_of% @OMA.S_oeis_a075125.main := by
  intro n hn
  have hL := Pa075125.gf_eq
  have ha : ∀ m, a m = coeff (m) ((X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6 + (-X ^ 2 - X ^ 3 + X ^ 4) * S) * (2 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6 + (-X ^ 2 - X ^ 3 + X ^ 4) * S) * (2 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (2) * A = (X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6) + (-X ^ 2 - X ^ 3 + X ^ 4) * S := by
    linear_combination hL
  have e := congrArg (coeff (n)) (Pa075125.ode S A Pa075125.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa075125.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa075125.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
