import OMAStatements.S_oeis_a105524
import Mathlib

open OMA.S_oeis_a105524
open PowerSeries

namespace Pa105524

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
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 + 4 * X ^ 2)
    (hL : (8 - 8 * X ^ 2 + 2 * X ^ 4) * A = (2 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 - 10 * X ^ 5 - 4 * X ^ 6 + 4 * X ^ 7) + (-2 * X ^ 2 - 4 * X ^ 3 + 5 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6) * S) :
    (-1416 - 264 * X - 2160 * X ^ 2 + 108 * X ^ 3 - 192 * X ^ 4) * (A) + (1264 + 24 * X + 2744 * X ^ 2 - 12 * X ^ 3 - 44 * X ^ 4) * (X * d⁄dX ℚ A) + (-330 - 921 * X ^ 2 + 192 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (26 + 91 * X ^ 2 - 52 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = 24 * X ^ 4 + 24 * X ^ 5 := by
  have hdD : d⁄dX ℚ (1 + 4 * X ^ 2 : PowerSeries ℚ) = 8 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (8 - 8 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ) = -16 * X + 8 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (2 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 - 10 * X ^ 5 - 4 * X ^ 6 + 4 * X ^ 7 : PowerSeries ℚ) = 4 * X + 12 * X ^ 2 + 28 * X ^ 3 - 50 * X ^ 4 - 24 * X ^ 5 + 28 * X ^ 6 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-2 * X ^ 2 - 4 * X ^ 3 + 5 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6 : PowerSeries ℚ) = -4 * X - 12 * X ^ 2 + 20 * X ^ 3 + 10 * X ^ 4 - 12 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (4 + 12 * X ^ 2 - 15 * X ^ 4 + 4 * X ^ 6) * (X * d⁄dX ℚ A) = (2 * X ^ 2 + 6 * X ^ 3 + 24 * X ^ 4 + 3 * X ^ 5 + 60 * X ^ 6 - 78 * X ^ 7 - 16 * X ^ 8 + 24 * X ^ 9) + (-2 * X ^ 2 - 6 * X ^ 3 - 4 * X ^ 4 - 31 * X ^ 5 + 40 * X ^ 6 + 8 * X ^ 7 - 12 * X ^ 8) * S := by
    have hg : (-8 + 4 * X ^ 2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-4 * X - 14 * X ^ 3 + 8 * X ^ 5) * E1 + (-8 * X ^ 2 - 32 * X ^ 4) * L0 + (4 * X ^ 3 + 8 * X ^ 4 - 12 * X ^ 5 - 8 * X ^ 6 + 9 * X ^ 7 + 2 * X ^ 8 - 2 * X ^ 9) * hS1
  have dP2 : d⁄dX ℚ (4 + 12 * X ^ 2 - 15 * X ^ 4 + 4 * X ^ 6 : PowerSeries ℚ) = 24 * X - 60 * X ^ 3 + 24 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (2 * X ^ 2 + 6 * X ^ 3 + 24 * X ^ 4 + 3 * X ^ 5 + 60 * X ^ 6 - 78 * X ^ 7 - 16 * X ^ 8 + 24 * X ^ 9 : PowerSeries ℚ) = 4 * X + 18 * X ^ 2 + 96 * X ^ 3 + 15 * X ^ 4 + 360 * X ^ 5 - 546 * X ^ 6 - 128 * X ^ 7 + 216 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (-2 * X ^ 2 - 6 * X ^ 3 - 4 * X ^ 4 - 31 * X ^ 5 + 40 * X ^ 6 + 8 * X ^ 7 - 12 * X ^ 8 : PowerSeries ℚ) = -4 * X - 18 * X ^ 2 - 16 * X ^ 3 - 155 * X ^ 4 + 240 * X ^ 5 + 56 * X ^ 6 - 96 * X ^ 7 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (-8 - 52 * X ^ 2 - 38 * X ^ 4 + 145 * X ^ 6 - 88 * X ^ 8 + 16 * X ^ 10) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (-8 * X ^ 2 - 36 * X ^ 3 - 196 * X ^ 4 - 84 * X ^ 5 - 1136 * X ^ 6 + 951 * X ^ 7 - 1736 * X ^ 8 + 2442 * X ^ 9 + 704 * X ^ 10 - 1536 * X ^ 11 - 128 * X ^ 12 + 288 * X ^ 13) + (8 * X ^ 2 + 36 * X ^ 3 + 52 * X ^ 4 + 412 * X ^ 5 - 360 * X ^ 6 + 897 * X ^ 7 - 1312 * X ^ 8 - 360 * X ^ 9 + 784 * X ^ 10 + 64 * X ^ 11 - 144 * X ^ 12) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-4 * X - 14 * X ^ 3 + 8 * X ^ 5) * E2 + (24 * X ^ 2 - 48 * X ^ 4) * L1 + (4 * X ^ 3 + 12 * X ^ 4 + 6 * X ^ 5 + 56 * X ^ 6 - 84 * X ^ 7 - 47 * X ^ 8 + 64 * X ^ 9 + 8 * X ^ 10 - 12 * X ^ 11) * hS1
  have dP3 : d⁄dX ℚ (-8 - 52 * X ^ 2 - 38 * X ^ 4 + 145 * X ^ 6 - 88 * X ^ 8 + 16 * X ^ 10 : PowerSeries ℚ) = -104 * X - 152 * X ^ 3 + 870 * X ^ 5 - 704 * X ^ 7 + 160 * X ^ 9 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU3 : d⁄dX ℚ (-8 * X ^ 2 - 36 * X ^ 3 - 196 * X ^ 4 - 84 * X ^ 5 - 1136 * X ^ 6 + 951 * X ^ 7 - 1736 * X ^ 8 + 2442 * X ^ 9 + 704 * X ^ 10 - 1536 * X ^ 11 - 128 * X ^ 12 + 288 * X ^ 13 : PowerSeries ℚ) = -16 * X - 108 * X ^ 2 - 784 * X ^ 3 - 420 * X ^ 4 - 6816 * X ^ 5 + 6657 * X ^ 6 - 13888 * X ^ 7 + 21978 * X ^ 8 + 7040 * X ^ 9 - 16896 * X ^ 10 - 1536 * X ^ 11 + 3744 * X ^ 12 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV3 : d⁄dX ℚ (8 * X ^ 2 + 36 * X ^ 3 + 52 * X ^ 4 + 412 * X ^ 5 - 360 * X ^ 6 + 897 * X ^ 7 - 1312 * X ^ 8 - 360 * X ^ 9 + 784 * X ^ 10 + 64 * X ^ 11 - 144 * X ^ 12 : PowerSeries ℚ) = 16 * X + 108 * X ^ 2 + 208 * X ^ 3 + 2060 * X ^ 4 - 2160 * X ^ 5 + 6279 * X ^ 6 - 10496 * X ^ 7 - 3240 * X ^ 8 + 7840 * X ^ 9 + 704 * X ^ 10 - 1728 * X ^ 11 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E3 := th_step _ _ _ _ _ L2
  simp only [dP3, dU3, dV3] at E3
  have L3 : (16 + 160 * X ^ 2 + 408 * X ^ 4 - 232 * X ^ 6 - 991 * X ^ 8 + 1164 * X ^ 10 - 464 * X ^ 12 + 64 * X ^ 14) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = (32 * X ^ 2 + 216 * X ^ 3 + 1472 * X ^ 4 + 660 * X ^ 5 + 14280 * X ^ 6 - 11550 * X ^ 7 + 50656 * X ^ 8 - 64149 * X ^ 9 + 56176 * X ^ 10 - 67974 * X ^ 11 - 14016 * X ^ 12 + 61080 * X ^ 13 + 7424 * X ^ 14 - 24864 * X ^ 15 - 1024 * X ^ 16 + 3456 * X ^ 17) + (-32 * X ^ 2 - 216 * X ^ 3 - 384 * X ^ 4 - 4228 * X ^ 5 + 3576 * X ^ 6 - 20426 * X ^ 7 + 28592 * X ^ 8 - 27919 * X ^ 9 + 38496 * X ^ 10 + 7616 * X ^ 11 - 32064 * X ^ 12 - 3776 * X ^ 13 + 12640 * X ^ 14 + 512 * X ^ 15 - 1728 * X ^ 16) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-4 * X - 14 * X ^ 3 + 8 * X ^ 5) * E3 + (52 * X ^ 2 - 80 * X ^ 4) * L2 + (-16 * X ^ 3 - 72 * X ^ 4 - 96 * X ^ 5 - 788 * X ^ 6 + 772 * X ^ 7 - 1382 * X ^ 8 + 2264 * X ^ 9 + 1617 * X ^ 10 - 2880 * X ^ 11 - 488 * X ^ 12 + 1072 * X ^ 13 + 64 * X ^ 14 - 144 * X ^ 15) * hS1
  have key : (32 + 320 * X ^ 2 + 816 * X ^ 4 - 464 * X ^ 6 - 1982 * X ^ 8 + 2328 * X ^ 10 - 928 * X ^ 12 + 128 * X ^ 14) * (((-1416 - 264 * X - 2160 * X ^ 2 + 108 * X ^ 3 - 192 * X ^ 4) * (A) + (1264 + 24 * X + 2744 * X ^ 2 - 12 * X ^ 3 - 44 * X ^ 4) * (X * d⁄dX ℚ A) + (-330 - 921 * X ^ 2 + 192 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (26 + 91 * X ^ 2 - 52 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A)))) - (24 * X ^ 4 + 24 * X ^ 5)) = 0 := by
    linear_combination (-5664 - 1056 * X - 70944 * X ^ 2 - 11184 * X ^ 3 - 301128 * X ^ 4 - 33528 * X ^ 5 - 429264 * X ^ 6 - 4404 * X ^ 7 + 102528 * X ^ 8 + 63120 * X ^ 9 + 344064 * X ^ 10 - 39360 * X ^ 11 - 98304 * X ^ 12 + 6912 * X ^ 13 - 12288 * X ^ 14) * L0 + (10112 + 192 * X + 92736 * X ^ 2 + 1248 * X ^ 3 + 236736 * X ^ 4 + 912 * X ^ 5 + 37072 * X ^ 6 - 3480 * X ^ 7 - 269784 * X ^ 8 + 2112 * X ^ 9 + 92736 * X ^ 10 - 384 * X ^ 11 - 1408 * X ^ 12) * L1 + (1320 + 8304 * X ^ 2 + 9486 * X ^ 4 - 10056 * X ^ 6 + 1536 * X ^ 8) * L2 + (52 + 182 * X ^ 2 - 104 * X ^ 4) * L3
  have hne : (32 + 320 * X ^ 2 + 816 * X ^ 4 - 464 * X ^ 6 - 1982 * X ^ 8 + 2328 * X ^ 10 - 928 * X ^ 12 + 128 * X ^ 14 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

theorem S_sq : S ^ 2 = 1 + 4 * X ^ 2 := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow h0, hB, ← coe_substAlgHom h0, map_add, map_one,
    coe_substAlgHom, subst_X h0, R]
  ring

theorem gf_eq : (8 - 8 * X ^ 2 + 2 * X ^ 4) * ((2 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 - 10 * X ^ 5 - 4 * X ^ 6 + 4 * X ^ 7 + (-2 * X ^ 2 - 4 * X ^ 3 + 5 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6) * S) * (8 - 8 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹) = 2 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 - 10 * X ^ 5 - 4 * X ^ 6 + 4 * X ^ 7 + (-2 * X ^ 2 - 4 * X ^ 3 + 5 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6) * S := by
  have hd : constantCoeff (8 - 8 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (8 - 8 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ) hd
  linear_combination (2 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 - 10 * X ^ 5 - 4 * X ^ 6 + 4 * X ^ 7 + (-2 * X ^ 2 - 4 * X ^ 3 + 5 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6) * S) * hinv

end Pa105524

theorem OMA.solution : type_of% @OMA.S_oeis_a105524.main := by
  intro n hn
  have hL := Pa105524.gf_eq
  have ha : ∀ m, a m = coeff ((m + 4)) ((2 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 - 10 * X ^ 5 - 4 * X ^ 6 + 4 * X ^ 7 + (-2 * X ^ 2 - 4 * X ^ 3 + 5 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6) * S) * (8 - 8 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((2 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 - 10 * X ^ 5 - 4 * X ^ 6 + 4 * X ^ 7 + (-2 * X ^ 2 - 4 * X ^ 3 + 5 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6) * S) * (8 - 8 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (8 - 8 * X ^ 2 + 2 * X ^ 4) * A = (2 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 - 10 * X ^ 5 - 4 * X ^ 6 + 4 * X ^ 7) + (-2 * X ^ 2 - 4 * X ^ 3 + 5 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6) * S := by
    linear_combination hL
  have e := congrArg (coeff ((n + 4))) (Pa105524.ode S A Pa105524.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa105524.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa105524.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
