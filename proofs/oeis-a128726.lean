import OMAStatements.S_oeis_a128726
import Mathlib

open OMA.S_oeis_a128726
open PowerSeries

namespace Pa128726

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
    (hL : (8 - 56 * X + 90 * X ^ 2 - 52 * X ^ 3 + 10 * X ^ 4) * A = (-2 + 15 * X - 29 * X ^ 2 + 21 * X ^ 3 - 5 * X ^ 4) + (2 - 9 * X + 6 * X ^ 2 - X ^ 3) * S) :
    (4 * X) * (A) + (18 - 38 * X - 5 * X ^ 2 - 5 * X ^ 3) * (X * d⁄dX ℚ A) + (-12 + 45 * X - 13 * X ^ 2 - 10 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (2 - 13 * X + 16 * X ^ 2 - 5 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = 0 := by
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
  have dP1 : d⁄dX ℚ (8 - 56 * X + 90 * X ^ 2 - 52 * X ^ 3 + 10 * X ^ 4 : PowerSeries ℚ) = -56 + 180 * X - 156 * X ^ 2 + 40 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (-2 + 15 * X - 29 * X ^ 2 + 21 * X ^ 3 - 5 * X ^ 4 : PowerSeries ℚ) = 15 - 58 * X + 63 * X ^ 2 - 20 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (2 - 9 * X + 6 * X ^ 2 - X ^ 3 : PowerSeries ℚ) = -9 + 12 * X - 3 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (8 - 104 * X + 466 * X ^ 2 - 872 * X ^ 3 + 772 * X ^ 4 - 320 * X ^ 5 + 50 * X ^ 6) * (X * d⁄dX ℚ A) = (X - 12 * X ^ 2 + 46 * X ^ 3 - 60 * X ^ 4 + 25 * X ^ 5) + (-X + 9 * X ^ 2 + 3 * X ^ 3 - 7 * X ^ 4) * S := by
    have hg : (-4 + 2 * X : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-4 * X + 26 * X ^ 2 - 32 * X ^ 3 + 10 * X ^ 4) * E1 + (-28 * X + 76 * X ^ 2 - 40 * X ^ 3) * L0 + (-4 * X + 20 * X ^ 2 - 21 * X ^ 3 + 8 * X ^ 4 - X ^ 5) * hS1
  have dP2 : d⁄dX ℚ (8 - 104 * X + 466 * X ^ 2 - 872 * X ^ 3 + 772 * X ^ 4 - 320 * X ^ 5 + 50 * X ^ 6 : PowerSeries ℚ) = -104 + 932 * X - 2616 * X ^ 2 + 3088 * X ^ 3 - 1600 * X ^ 4 + 300 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (X - 12 * X ^ 2 + 46 * X ^ 3 - 60 * X ^ 4 + 25 * X ^ 5 : PowerSeries ℚ) = 1 - 24 * X + 138 * X ^ 2 - 240 * X ^ 3 + 125 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (-X + 9 * X ^ 2 + 3 * X ^ 3 - 7 * X ^ 4 : PowerSeries ℚ) = -1 + 18 * X + 9 * X ^ 2 - 28 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (-16 + 312 * X - 2412 * X ^ 2 + 9506 * X ^ 3 - 20856 * X ^ 4 + 26958 * X ^ 5 - 20972 * X ^ 6 + 9630 * X ^ 7 - 2400 * X ^ 8 + 250 * X ^ 9) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (-2 * X + 35 * X ^ 2 - 228 * X ^ 3 + 669 * X ^ 4 - 834 * X ^ 5 + 285 * X ^ 6 + 200 * X ^ 7 - 125 * X ^ 8) + (2 * X - 29 * X ^ 2 + X ^ 3 + 304 * X ^ 4 - 350 * X ^ 5 + 61 * X ^ 6 + 35 * X ^ 7) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-4 * X + 26 * X ^ 2 - 32 * X ^ 3 + 10 * X ^ 4) * E2 + (-52 * X + 128 * X ^ 2 - 60 * X ^ 3) * L1 + (2 * X ^ 2 - 19 * X ^ 3 + 3 * X ^ 4 + 17 * X ^ 5 - 7 * X ^ 6) * hS1
  have dP3 : d⁄dX ℚ (-16 + 312 * X - 2412 * X ^ 2 + 9506 * X ^ 3 - 20856 * X ^ 4 + 26958 * X ^ 5 - 20972 * X ^ 6 + 9630 * X ^ 7 - 2400 * X ^ 8 + 250 * X ^ 9 : PowerSeries ℚ) = 312 - 4824 * X + 28518 * X ^ 2 - 83424 * X ^ 3 + 134790 * X ^ 4 - 125832 * X ^ 5 + 67410 * X ^ 6 - 19200 * X ^ 7 + 2250 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU3 : d⁄dX ℚ (-2 * X + 35 * X ^ 2 - 228 * X ^ 3 + 669 * X ^ 4 - 834 * X ^ 5 + 285 * X ^ 6 + 200 * X ^ 7 - 125 * X ^ 8 : PowerSeries ℚ) = -2 + 70 * X - 684 * X ^ 2 + 2676 * X ^ 3 - 4170 * X ^ 4 + 1710 * X ^ 5 + 1400 * X ^ 6 - 1000 * X ^ 7 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV3 : d⁄dX ℚ (2 * X - 29 * X ^ 2 + X ^ 3 + 304 * X ^ 4 - 350 * X ^ 5 + 61 * X ^ 6 + 35 * X ^ 7 : PowerSeries ℚ) = 2 - 58 * X + 3 * X ^ 2 + 1216 * X ^ 3 - 1750 * X ^ 4 + 366 * X ^ 5 + 245 * X ^ 6 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E3 := th_step _ _ _ _ _ L2
  simp only [dP3, dU3, dV3] at E3
  have L3 : (32 - 832 * X + 9136 * X ^ 2 - 55440 * X ^ 3 + 205442 * X ^ 4 - 489200 * X ^ 5 + 773624 * X ^ 6 - 827504 * X ^ 7 + 600332 * X ^ 8 - 290640 * X ^ 9 + 89800 * X ^ 10 - 16000 * X ^ 11 + 1250 * X ^ 12) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = (4 * X - 88 * X ^ 2 + 753 * X ^ 3 - 3032 * X ^ 4 + 4868 * X ^ 5 + 3144 * X ^ 6 - 21754 * X ^ 7 + 29080 * X ^ 8 - 15600 * X ^ 9 + 2000 * X ^ 10 + 625 * X ^ 11) + (-4 * X + 76 * X ^ 2 + 331 * X ^ 3 - 3975 * X ^ 4 + 10181 * X ^ 5 - 6181 * X ^ 6 - 4875 * X ^ 7 + 6487 * X ^ 8 - 1625 * X ^ 9 - 175 * X ^ 10) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-4 * X + 26 * X ^ 2 - 32 * X ^ 3 + 10 * X ^ 4) * E3 + (-78 * X + 192 * X ^ 2 - 90 * X ^ 3) * L2 + (-4 * X ^ 2 + 60 * X ^ 3 - 31 * X ^ 4 - 607 * X ^ 5 + 1004 * X ^ 6 - 472 * X ^ 7 - 9 * X ^ 8 + 35 * X ^ 9) * hS1
  have key : (32 - 832 * X + 9136 * X ^ 2 - 55440 * X ^ 3 + 205442 * X ^ 4 - 489200 * X ^ 5 + 773624 * X ^ 6 - 827504 * X ^ 7 + 600332 * X ^ 8 - 290640 * X ^ 9 + 89800 * X ^ 10 - 16000 * X ^ 11 + 1250 * X ^ 12) * (((4 * X) * (A) + (18 - 38 * X - 5 * X ^ 2 - 5 * X ^ 3) * (X * d⁄dX ℚ A) + (-12 + 45 * X - 13 * X ^ 2 - 10 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (2 - 13 * X + 16 * X ^ 2 - 5 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A)))) - (0)) = 0 := by
    linear_combination (16 * X - 304 * X ^ 2 + 2260 * X ^ 3 - 8376 * X ^ 4 + 16668 * X ^ 5 - 18624 * X ^ 6 + 11660 * X ^ 7 - 3800 * X ^ 8 + 500 * X ^ 9) * L0 + (72 - 1088 * X + 6150 * X ^ 2 - 16462 * X ^ 3 + 22611 * X ^ 4 - 16533 * X ^ 5 + 6780 * X ^ 6 - 2080 * X ^ 7 + 675 * X ^ 8 - 125 * X ^ 9) * L1 + (24 - 246 * X + 803 * X ^ 2 - 929 * X ^ 3 + 303 * X ^ 4 + 95 * X ^ 5 - 50 * X ^ 6) * L2 + (2 - 13 * X + 16 * X ^ 2 - 5 * X ^ 3) * L3
  have hne : (32 - 832 * X + 9136 * X ^ 2 - 55440 * X ^ 3 + 205442 * X ^ 4 - 489200 * X ^ 5 + 773624 * X ^ 6 - 827504 * X ^ 7 + 600332 * X ^ 8 - 290640 * X ^ 9 + 89800 * X ^ 10 - 16000 * X ^ 11 + 1250 * X ^ 12 : PowerSeries ℚ) ≠ 0 := by
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

theorem gf_eq : (8 - 56 * X + 90 * X ^ 2 - 52 * X ^ 3 + 10 * X ^ 4) * ((-2 + 15 * X - 29 * X ^ 2 + 21 * X ^ 3 - 5 * X ^ 4 + (2 - 9 * X + 6 * X ^ 2 - X ^ 3) * S) * (8 - 56 * X + 90 * X ^ 2 - 52 * X ^ 3 + 10 * X ^ 4 : PowerSeries ℚ)⁻¹) = -2 + 15 * X - 29 * X ^ 2 + 21 * X ^ 3 - 5 * X ^ 4 + (2 - 9 * X + 6 * X ^ 2 - X ^ 3) * S := by
  have hd : constantCoeff (8 - 56 * X + 90 * X ^ 2 - 52 * X ^ 3 + 10 * X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (8 - 56 * X + 90 * X ^ 2 - 52 * X ^ 3 + 10 * X ^ 4 : PowerSeries ℚ) hd
  linear_combination (-2 + 15 * X - 29 * X ^ 2 + 21 * X ^ 3 - 5 * X ^ 4 + (2 - 9 * X + 6 * X ^ 2 - X ^ 3) * S) * hinv

end Pa128726

theorem OMA.solution : type_of% @OMA.S_oeis_a128726.main := by
  intro n hn
  have hL := Pa128726.gf_eq
  have ha : ∀ m, a m = coeff (m) ((-2 + 15 * X - 29 * X ^ 2 + 21 * X ^ 3 - 5 * X ^ 4 + (2 - 9 * X + 6 * X ^ 2 - X ^ 3) * S) * (8 - 56 * X + 90 * X ^ 2 - 52 * X ^ 3 + 10 * X ^ 4 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((-2 + 15 * X - 29 * X ^ 2 + 21 * X ^ 3 - 5 * X ^ 4 + (2 - 9 * X + 6 * X ^ 2 - X ^ 3) * S) * (8 - 56 * X + 90 * X ^ 2 - 52 * X ^ 3 + 10 * X ^ 4 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (8 - 56 * X + 90 * X ^ 2 - 52 * X ^ 3 + 10 * X ^ 4) * A = (-2 + 15 * X - 29 * X ^ 2 + 21 * X ^ 3 - 5 * X ^ 4) + (2 - 9 * X + 6 * X ^ 2 - X ^ 3) * S := by
    linear_combination hL
  have e := congrArg (coeff (n)) (Pa128726.ode S A Pa128726.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa128726.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa128726.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
