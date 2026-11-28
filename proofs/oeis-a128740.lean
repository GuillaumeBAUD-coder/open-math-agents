import OMAStatements.S_oeis_a128740
import Mathlib

open OMA.S_oeis_a128740
open PowerSeries

namespace Pa128740

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
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2)
    (hL : (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3) * A = (-2 * X + 15 * X ^ 2 - 29 * X ^ 3 + 21 * X ^ 4 - 5 * X ^ 5) + (2 * X - 9 * X ^ 2 + 6 * X ^ 3 - X ^ 4) * S) :
    (-38 + 140 * X - 40 * X ^ 2 - 10 * X ^ 3) * (A) + (56 - 211 * X + 126 * X ^ 2 - 5 * X ^ 3) * (X * d⁄dX ℚ A) + (-20 + 99 * X - 88 * X ^ 2 + 15 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (2 - 13 * X + 16 * X ^ 2 - 5 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = -6 * X ^ 4 := by
  have hdD : d⁄dX ℚ (1 - 6 * X + 5 * X ^ 2 : PowerSeries ℚ) = -6 + 10 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ) = -48 + 84 * X - 30 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (-2 * X + 15 * X ^ 2 - 29 * X ^ 3 + 21 * X ^ 4 - 5 * X ^ 5 : PowerSeries ℚ) = -2 + 30 * X - 87 * X ^ 2 + 84 * X ^ 3 - 25 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (2 * X - 9 * X ^ 2 + 6 * X ^ 3 - X ^ 4 : PowerSeries ℚ) = 2 - 18 * X + 18 * X ^ 2 - 4 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (-4 + 48 * X - 185 * X ^ 2 + 251 * X ^ 3 - 135 * X ^ 4 + 25 * X ^ 5) * (X * d⁄dX ℚ A) = (X - 15 * X ^ 2 + 83 * X ^ 3 - 210 * X ^ 4 + 251 * X ^ 5 - 135 * X ^ 6 + 25 * X ^ 7) + (-X + 12 * X ^ 2 - 49 * X ^ 3 + 65 * X ^ 4 - 30 * X ^ 5 + 5 * X ^ 6) * S := by
    have hg : (-8 + 4 * X : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (4 * X - 26 * X ^ 2 + 32 * X ^ 3 - 10 * X ^ 4) * E1 + (24 * X - 54 * X ^ 2 + 30 * X ^ 3) * L0 + (4 * X ^ 2 - 20 * X ^ 3 + 21 * X ^ 4 - 8 * X ^ 5 + X ^ 6) * hS1
  have dP2 : d⁄dX ℚ (-4 + 48 * X - 185 * X ^ 2 + 251 * X ^ 3 - 135 * X ^ 4 + 25 * X ^ 5 : PowerSeries ℚ) = 48 - 370 * X + 753 * X ^ 2 - 540 * X ^ 3 + 125 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (X - 15 * X ^ 2 + 83 * X ^ 3 - 210 * X ^ 4 + 251 * X ^ 5 - 135 * X ^ 6 + 25 * X ^ 7 : PowerSeries ℚ) = 1 - 30 * X + 249 * X ^ 2 - 840 * X ^ 3 + 1255 * X ^ 4 - 810 * X ^ 5 + 175 * X ^ 6 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (-X + 12 * X ^ 2 - 49 * X ^ 3 + 65 * X ^ 4 - 30 * X ^ 5 + 5 * X ^ 6 : PowerSeries ℚ) = -1 + 24 * X - 147 * X ^ 2 + 260 * X ^ 3 - 150 * X ^ 4 + 30 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (8 - 148 * X + 1058 * X ^ 2 - 3695 * X ^ 3 + 6733 * X ^ 4 - 6746 * X ^ 5 + 3740 * X ^ 6 - 1075 * X ^ 7 + 125 * X ^ 8) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (-2 * X + 49 * X ^ 2 - 491 * X ^ 3 + 2590 * X ^ 4 - 7750 * X ^ 5 + 13391 * X ^ 6 - 13367 * X ^ 7 + 7480 * X ^ 8 - 2150 * X ^ 9 + 250 * X ^ 10) + (2 * X - 43 * X ^ 2 + 366 * X ^ 3 - 1438 * X ^ 4 + 2782 * X ^ 5 - 2785 * X ^ 6 + 1500 * X ^ 7 - 430 * X ^ 8 + 50 * X ^ 9) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-4 * X + 26 * X ^ 2 - 32 * X ^ 3 + 10 * X ^ 4) * E2 + (-48 * X + 106 * X ^ 2 - 50 * X ^ 3) * L1 + (2 * X ^ 2 - 25 * X ^ 3 + 110 * X ^ 4 - 179 * X ^ 5 + 125 * X ^ 6 - 40 * X ^ 7 + 5 * X ^ 8) * hS1
  have dP3 : d⁄dX ℚ (8 - 148 * X + 1058 * X ^ 2 - 3695 * X ^ 3 + 6733 * X ^ 4 - 6746 * X ^ 5 + 3740 * X ^ 6 - 1075 * X ^ 7 + 125 * X ^ 8 : PowerSeries ℚ) = -148 + 2116 * X - 11085 * X ^ 2 + 26932 * X ^ 3 - 33730 * X ^ 4 + 22440 * X ^ 5 - 7525 * X ^ 6 + 1000 * X ^ 7 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU3 : d⁄dX ℚ (-2 * X + 49 * X ^ 2 - 491 * X ^ 3 + 2590 * X ^ 4 - 7750 * X ^ 5 + 13391 * X ^ 6 - 13367 * X ^ 7 + 7480 * X ^ 8 - 2150 * X ^ 9 + 250 * X ^ 10 : PowerSeries ℚ) = -2 + 98 * X - 1473 * X ^ 2 + 10360 * X ^ 3 - 38750 * X ^ 4 + 80346 * X ^ 5 - 93569 * X ^ 6 + 59840 * X ^ 7 - 19350 * X ^ 8 + 2500 * X ^ 9 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV3 : d⁄dX ℚ (2 * X - 43 * X ^ 2 + 366 * X ^ 3 - 1438 * X ^ 4 + 2782 * X ^ 5 - 2785 * X ^ 6 + 1500 * X ^ 7 - 430 * X ^ 8 + 50 * X ^ 9 : PowerSeries ℚ) = 2 - 86 * X + 1098 * X ^ 2 - 5752 * X ^ 3 + 13910 * X ^ 4 - 16710 * X ^ 5 + 10500 * X ^ 6 - 3440 * X ^ 7 + 450 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E3 := th_step _ _ _ _ _ L2
  simp only [dP3, dU3, dV3] at E3
  have L3 : (-16 + 400 * X - 4168 * X ^ 2 + 23552 * X ^ 3 - 79169 * X ^ 4 + 165431 * X ^ 5 - 221381 * X ^ 6 + 192371 * X ^ 7 - 107795 * X ^ 8 + 37525 * X ^ 9 - 7375 * X ^ 10 + 625 * X ^ 11) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = (4 * X - 148 * X ^ 2 + 2269 * X ^ 3 - 19035 * X ^ 4 + 96713 * X ^ 5 - 311027 * X ^ 6 + 645619 * X ^ 7 - 872549 * X ^ 8 + 766859 * X ^ 9 - 431805 * X ^ 10 + 150100 * X ^ 11 - 29500 * X ^ 12 + 2500 * X ^ 13) + (-4 * X + 136 * X ^ 2 - 1869 * X ^ 3 + 12652 * X ^ 4 - 48159 * X ^ 5 + 109184 * X ^ 6 - 152581 * X ^ 7 + 135900 * X ^ 8 - 78365 * X ^ 9 + 28380 * X ^ 10 - 5750 * X ^ 11 + 500 * X ^ 12) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-4 * X + 26 * X ^ 2 - 32 * X ^ 3 + 10 * X ^ 4) * E3 + (-74 * X + 170 * X ^ 2 - 80 * X ^ 3) * L2 + (-4 * X ^ 2 + 88 * X ^ 3 - 775 * X ^ 4 + 3242 * X ^ 5 - 7002 * X ^ 6 + 8352 * X ^ 7 - 5785 * X ^ 8 + 2360 * X ^ 9 - 530 * X ^ 10 + 50 * X ^ 11) * hS1
  have key : (32 - 800 * X + 8336 * X ^ 2 - 47104 * X ^ 3 + 158338 * X ^ 4 - 330862 * X ^ 5 + 442762 * X ^ 6 - 384742 * X ^ 7 + 215590 * X ^ 8 - 75050 * X ^ 9 + 14750 * X ^ 10 - 1250 * X ^ 11) * (((-38 + 140 * X - 40 * X ^ 2 - 10 * X ^ 3) * (A) + (56 - 211 * X + 126 * X ^ 2 - 5 * X ^ 3) * (X * d⁄dX ℚ A) + (-20 + 99 * X - 88 * X ^ 2 + 15 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (2 - 13 * X + 16 * X ^ 2 - 5 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A)))) - (-6 * X ^ 4)) = 0 := by
    linear_combination (-152 + 3448 * X - 32270 * X ^ 2 + 161672 * X ^ 3 - 473346 * X ^ 4 + 838418 * X ^ 5 - 908350 * X ^ 6 + 588770 * X ^ 7 - 207790 * X ^ 8 + 26350 * X ^ 9 + 4500 * X ^ 10 - 1250 * X ^ 11) * L0 + (-448 + 7512 * X - 49048 * X ^ 2 + 160302 * X ^ 3 - 286460 * X ^ 4 + 293014 * X ^ 5 - 171952 * X ^ 6 + 54730 * X ^ 7 - 7900 * X ^ 8 + 250 * X ^ 9) * L1 + (-80 + 916 * X - 3566 * X ^ 2 + 5716 * X ^ 3 - 4196 * X ^ 4 + 1360 * X ^ 5 - 150 * X ^ 6) * L2 + (-4 + 26 * X - 32 * X ^ 2 + 10 * X ^ 3) * L3
  have hne : (32 - 800 * X + 8336 * X ^ 2 - 47104 * X ^ 3 + 158338 * X ^ 4 - 330862 * X ^ 5 + 442762 * X ^ 6 - 384742 * X ^ 7 + 215590 * X ^ 8 - 75050 * X ^ 9 + 14750 * X ^ 10 - 1250 * X ^ 11 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

theorem S_sq : S ^ 2 = 1 - 6 * X + 5 * X ^ 2 := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow h0, hB, ← coe_substAlgHom h0, map_add, map_one,
    coe_substAlgHom, subst_X h0, R]
  ring

theorem gf_eq : (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3) * ((-2 * X + 15 * X ^ 2 - 29 * X ^ 3 + 21 * X ^ 4 - 5 * X ^ 5 + (2 * X - 9 * X ^ 2 + 6 * X ^ 3 - X ^ 4) * S) * (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ)⁻¹) = -2 * X + 15 * X ^ 2 - 29 * X ^ 3 + 21 * X ^ 4 - 5 * X ^ 5 + (2 * X - 9 * X ^ 2 + 6 * X ^ 3 - X ^ 4) * S := by
  have hd : constantCoeff (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ) hd
  linear_combination (-2 * X + 15 * X ^ 2 - 29 * X ^ 3 + 21 * X ^ 4 - 5 * X ^ 5 + (2 * X - 9 * X ^ 2 + 6 * X ^ 3 - X ^ 4) * S) * hinv

end Pa128740

theorem OMA.solution : type_of% @OMA.S_oeis_a128740.main := by
  intro n hn
  have hL := Pa128740.gf_eq
  have ha : ∀ m, a m = coeff ((m + 2)) ((-2 * X + 15 * X ^ 2 - 29 * X ^ 3 + 21 * X ^ 4 - 5 * X ^ 5 + (2 * X - 9 * X ^ 2 + 6 * X ^ 3 - X ^ 4) * S) * (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((-2 * X + 15 * X ^ 2 - 29 * X ^ 3 + 21 * X ^ 4 - 5 * X ^ 5 + (2 * X - 9 * X ^ 2 + 6 * X ^ 3 - X ^ 4) * S) * (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3) * A = (-2 * X + 15 * X ^ 2 - 29 * X ^ 3 + 21 * X ^ 4 - 5 * X ^ 5) + (2 * X - 9 * X ^ 2 + 6 * X ^ 3 - X ^ 4) * S := by
    linear_combination hL
  have e := congrArg (coeff ((n + 2))) (Pa128740.ode S A Pa128740.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa128740.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa128740.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
