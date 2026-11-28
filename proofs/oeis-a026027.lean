import OMAStatements.S_oeis_a026027
import Mathlib

open OMA.S_oeis_a026027
open PowerSeries

namespace Pa026027

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
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 4 * X)
    (hL : (2) * A = (X ^ 5 - 9 * X ^ 6 + 28 * X ^ 7 - 35 * X ^ 8 + 14 * X ^ 9) + (-X ^ 5 + 7 * X ^ 6 - 16 * X ^ 7 + 13 * X ^ 8 - 2 * X ^ 9) * S) :
    (60 + 6284 * X - 41748 * X ^ 2 + 52668 * X ^ 3) * (A) + (-77 - 1203 * X + 8656 * X ^ 2 - 11092 * X ^ 3) * (X * d⁄dX ℚ A) + (13 + 13 * X - 406 * X ^ 2 + 584 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = 1008 * X ^ 12 := by
  have hdD : d⁄dX ℚ (1 - 4 * X : PowerSeries ℚ) = -4 := by
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
  have dU1 : d⁄dX ℚ (X ^ 5 - 9 * X ^ 6 + 28 * X ^ 7 - 35 * X ^ 8 + 14 * X ^ 9 : PowerSeries ℚ) = 5 * X ^ 4 - 54 * X ^ 5 + 196 * X ^ 6 - 280 * X ^ 7 + 126 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-X ^ 5 + 7 * X ^ 6 - 16 * X ^ 7 + 13 * X ^ 8 - 2 * X ^ 9 : PowerSeries ℚ) = -5 * X ^ 4 + 42 * X ^ 5 - 112 * X ^ 6 + 104 * X ^ 7 - 18 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (2 - 8 * X) * (X * d⁄dX ℚ A) = (5 * X ^ 5 - 74 * X ^ 6 + 412 * X ^ 7 - 1064 * X ^ 8 + 1246 * X ^ 9 - 504 * X ^ 10) + (-5 * X ^ 5 + 64 * X ^ 6 - 294 * X ^ 7 + 584 * X ^ 8 - 460 * X ^ 9 + 76 * X ^ 10) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 8 * X ^ 2) * E1 + (0) * L0 + (-X ^ 6 + 7 * X ^ 7 - 16 * X ^ 8 + 13 * X ^ 9 - 2 * X ^ 10) * hS1
  have dP2 : d⁄dX ℚ (2 - 8 * X : PowerSeries ℚ) = -8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (5 * X ^ 5 - 74 * X ^ 6 + 412 * X ^ 7 - 1064 * X ^ 8 + 1246 * X ^ 9 - 504 * X ^ 10 : PowerSeries ℚ) = 25 * X ^ 4 - 444 * X ^ 5 + 2884 * X ^ 6 - 8512 * X ^ 7 + 11214 * X ^ 8 - 5040 * X ^ 9 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (-5 * X ^ 5 + 64 * X ^ 6 - 294 * X ^ 7 + 584 * X ^ 8 - 460 * X ^ 9 + 76 * X ^ 10 : PowerSeries ℚ) = -25 * X ^ 4 + 384 * X ^ 5 - 2058 * X ^ 6 + 4672 * X ^ 7 - 4140 * X ^ 8 + 760 * X ^ 9 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (-2 + 16 * X - 32 * X ^ 2) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (-25 * X ^ 5 + 524 * X ^ 6 - 4364 * X ^ 7 + 18400 * X ^ 8 - 41006 * X ^ 9 + 44912 * X ^ 10 - 18144 * X ^ 11) + (25 * X ^ 5 - 474 * X ^ 6 + 3466 * X ^ 7 - 12316 * X ^ 8 + 21660 * X ^ 9 - 16400 * X ^ 10 + 2888 * X ^ 11) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-2 * X + 8 * X ^ 2) * E2 + (-8 * X) * L1 + (5 * X ^ 6 - 64 * X ^ 7 + 294 * X ^ 8 - 584 * X ^ 9 + 460 * X ^ 10 - 76 * X ^ 11) * hS1
  have key : (2 - 16 * X + 32 * X ^ 2) * (((60 + 6284 * X - 41748 * X ^ 2 + 52668 * X ^ 3) * (A) + (-77 - 1203 * X + 8656 * X ^ 2 - 11092 * X ^ 3) * (X * d⁄dX ℚ A) + (13 + 13 * X - 406 * X ^ 2 + 584 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ A))) - (1008 * X ^ 12)) = 0 := by
    linear_combination (60 + 5804 * X - 91060 * X ^ 2 + 487196 * X ^ 3 - 1089312 * X ^ 4 + 842688 * X ^ 5) * L0 + (-77 - 895 * X + 13468 * X ^ 2 - 45716 * X ^ 3 + 44368 * X ^ 4) * L1 + (-13 - 13 * X + 406 * X ^ 2 - 584 * X ^ 3) * L2
  have hne : (2 - 16 * X + 32 * X ^ 2 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

theorem S_sq : S ^ 2 = 1 - 4 * X := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow h0, hB, ← coe_substAlgHom h0, map_add, map_one,
    coe_substAlgHom, subst_X h0, R]
  ring

theorem gf_eq : (2) * ((X ^ 5 - 9 * X ^ 6 + 28 * X ^ 7 - 35 * X ^ 8 + 14 * X ^ 9 + (-X ^ 5 + 7 * X ^ 6 - 16 * X ^ 7 + 13 * X ^ 8 - 2 * X ^ 9) * S) * (2 : PowerSeries ℚ)⁻¹) = X ^ 5 - 9 * X ^ 6 + 28 * X ^ 7 - 35 * X ^ 8 + 14 * X ^ 9 + (-X ^ 5 + 7 * X ^ 6 - 16 * X ^ 7 + 13 * X ^ 8 - 2 * X ^ 9) * S := by
  have hd : constantCoeff (2 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 : PowerSeries ℚ) hd
  linear_combination (X ^ 5 - 9 * X ^ 6 + 28 * X ^ 7 - 35 * X ^ 8 + 14 * X ^ 9 + (-X ^ 5 + 7 * X ^ 6 - 16 * X ^ 7 + 13 * X ^ 8 - 2 * X ^ 9) * S) * hinv

end Pa026027

theorem OMA.solution : type_of% @OMA.S_oeis_a026027.main := by
  intro n hn
  have hL := Pa026027.gf_eq
  have ha : ∀ m, a m = coeff ((m + 10)) ((X ^ 5 - 9 * X ^ 6 + 28 * X ^ 7 - 35 * X ^ 8 + 14 * X ^ 9 + (-X ^ 5 + 7 * X ^ 6 - 16 * X ^ 7 + 13 * X ^ 8 - 2 * X ^ 9) * S) * (2 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((X ^ 5 - 9 * X ^ 6 + 28 * X ^ 7 - 35 * X ^ 8 + 14 * X ^ 9 + (-X ^ 5 + 7 * X ^ 6 - 16 * X ^ 7 + 13 * X ^ 8 - 2 * X ^ 9) * S) * (2 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (2) * A = (X ^ 5 - 9 * X ^ 6 + 28 * X ^ 7 - 35 * X ^ 8 + 14 * X ^ 9) + (-X ^ 5 + 7 * X ^ 6 - 16 * X ^ 7 + 13 * X ^ 8 - 2 * X ^ 9) * S := by
    linear_combination hL
  have e := congrArg (coeff ((n + 10))) (Pa026027.ode S A Pa026027.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa026027.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa026027.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
