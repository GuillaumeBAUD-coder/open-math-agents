import OMAStatements.S_oeis_a128734
import Mathlib

-- Problem: A128734: Number of LDs in all skew Dyck paths of semilength n.
-- Upstream: formal-conjectures statements/oeis-a128734.lean (declaration OMA.S_oeis_a128734.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a128734

open OMA.S_oeis_a128734 PowerSeries

theorem hR1 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])

theorem S_sq : S ^ 2 = R := by
  have h : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = 1 + X := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    have h12 : (1 / 2 + 1 / 2 : ℚ) = ((1 : ℕ) : ℚ) := by norm_num
    rw [h12, PowerSeries.binomialSeries_nat, pow_one]
  unfold S
  rw [← coe_substAlgHom hR1, ← map_pow, h, map_add, map_one, substAlgHom_X]
  ring

theorem ode : 2 * R * d⁄dX ℚ S = d⁄dX ℚ R * S := by
  have h := congrArg (d⁄dX ℚ) S_sq
  rw [pow_two, Derivation.leibniz, smul_eq_mul] at h
  rw [← h, ← S_sq]
  ring

theorem hRC : R = C (1 : ℚ) + C (-6 : ℚ) * X ^ 1 + C (5 : ℚ) * X ^ 2 := by
  simp only [R, map_one, map_neg, map_ofNat]
  ring

theorem hDR : d⁄dX ℚ R = C (-6 : ℚ) + C (10 : ℚ) * X ^ 1 := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  push_cast
  ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-12 : ℚ) * X ^ 1 * d⁄dX ℚ S + C (10 : ℚ) * X ^ 2 * d⁄dX ℚ S - (C (-6 : ℚ) * S + C (10 : ℚ) * X ^ 1 * S) = 0 := by
  have h := ode
  rw [hDR, hRC] at h
  simp only [map_one, map_neg, map_ofNat] at h ⊢
  linear_combination h

theorem cx (c : ℚ) (j n : ℕ) (f : ℚ⟦X⟧) (h : j ≤ n) :
    coeff n (C c * X ^ j * f) = c * coeff (n - j) f := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos h]

theorem cx0 (c : ℚ) (n : ℕ) (f : ℚ⟦X⟧) : coeff n (C c * f) = c * coeff n f := coeff_C_mul _ _ _

theorem cc (c : ℚ) (j n : ℕ) (h : n ≠ j) : coeff n (C c * X ^ j) = 0 := by
  rw [coeff_C_mul_X_pow, if_neg h]

theorem cc0 (c : ℚ) (n : ℕ) (h : n ≠ 0) : coeff n (C c : ℚ⟦X⟧) = 0 := by
  rw [coeff_C, if_neg h]

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 3) S * ((m : ℚ) + 3)) + (-12 : ℚ) * (coeff (m + 2) S * ((m : ℚ) + 2)) + (10 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-6 : ℚ) * coeff (m + 2) S + (10 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 2)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((-2 * X + 17 * X ^ 2 - 40 * X ^ 3 + 26 * X ^ 4 - 5 * X ^ 5 + (2 * X - 11 * X ^ 2 + 11 * X ^ 3 - 3 * X ^ 4) * S) * (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff (n + 2) F := rfl

theorem hF : F * (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : ℚ⟦X⟧) = -2 * X + 17 * X ^ 2 - 40 * X ^ 3 + 26 * X ^ 4 - 5 * X ^ 5 + (2 * X - 11 * X ^ 2 + 11 * X ^ 3 - 3 * X ^ 4) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : ℚ⟦X⟧) = C (8 : ℚ) + C (-48 : ℚ) * X ^ 1 + C (42 : ℚ) * X ^ 2 + C (-10 : ℚ) * X ^ 3 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (8 : ℚ) * F + C (-48 : ℚ) * X ^ 1 * F + C (42 : ℚ) * X ^ 2 * F + C (-10 : ℚ) * X ^ 3 * F - (C (2 : ℚ) * X ^ 1 * S + C (-11 : ℚ) * X ^ 2 * S + C (11 : ℚ) * X ^ 3 * S + C (-3 : ℚ) * X ^ 4 * S) - (C (-2 : ℚ) * X ^ 1 + C (17 : ℚ) * X ^ 2 + C (-40 : ℚ) * X ^ 3 + C (26 : ℚ) * X ^ 4 + C (-5 : ℚ) * X ^ 5) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (8 : ℚ) * coeff (m + 6) F + (-48 : ℚ) * coeff (m + 5) F + (42 : ℚ) * coeff (m + 4) F + (-10 : ℚ) * coeff (m + 3) F - ((2 : ℚ) * coeff (m + 5) S + (-11 : ℚ) * coeff (m + 4) S + (11 : ℚ) * coeff (m + 3) S + (-3 : ℚ) * coeff (m + 2) S) = 0 := by
  have h := congrArg (coeff (m + 6)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 6 - 1 = m + 5 from by omega, show m + 6 - 2 = m + 4 from by omega, show m + 6 - 3 = m + 3 from by omega, show m + 6 - 4 = m + 2 from by omega] at h
  linear_combination h

theorem cz (c : ℚ) (j n : ℕ) (f : ℚ⟦X⟧) (h : n < j) : coeff n (C c * X ^ j * f) = 0 := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_neg (by omega), mul_zero]

theorem ccj (c : ℚ) (j n : ℕ) (h : n = j) : coeff n (C c * X ^ j) = c := by
  rw [coeff_C_mul_X_pow, if_pos h]

theorem cc0' (c : ℚ) : coeff 0 (C c : ℚ⟦X⟧) = c := by rw [coeff_C, if_pos rfl]

theorem S_const : constantCoeff S = 1 := by
  have h0 : constantCoeff (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - 1) = 0 := by simp
  have hc : constantCoeff (R - 1) = 0 := by simp [R]
  have h1 := constantCoeff_subst_eq_zero (a := (R - 1 : ℚ⟦X⟧)) hc _ h0
  have h2 : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - 1).subst (R - 1) = S - 1 := by
    unfold S
    rw [← coe_substAlgHom hR1, map_sub, map_one]
  rw [h2] at h1
  have h3 : constantCoeff (S - 1) = 0 := h1
  rw [map_sub, map_one, sub_eq_zero] at h3
  exact h3

theorem hs0 : coeff 0 S = 1 := by rw [coeff_zero_eq_constantCoeff_apply, S_const]

theorem hs1 : coeff 1 S = (-3 : ℚ) := by
  have h := congrArg (coeff 0) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0] at h ⊢ <;> linarith

theorem hs2 : coeff 2 S = (-2 : ℚ) := by
  have h := congrArg (coeff 1) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1] at h ⊢ <;> linarith

theorem hs3 : coeff 3 S = (-6 : ℚ) := by
  have h := congrArg (coeff 2) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2] at h ⊢ <;> linarith

theorem hs4 : coeff 4 S = (-20 : ℚ) := by
  have h := congrArg (coeff 3) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3] at h ⊢ <;> linarith

theorem hs5 : coeff 5 S = (-72 : ℚ) := by
  have h := congrArg (coeff 4) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4] at h ⊢ <;> linarith

theorem hs6 : coeff 6 S = (-274 : ℚ) := by
  have h := congrArg (coeff 5) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5] at h ⊢ <;> linarith

theorem hs7 : coeff 7 S = (-1086 : ℚ) := by
  have h := congrArg (coeff 6) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at h ⊢ <;> linarith

theorem hs8 : coeff 8 S = (-4438 : ℚ) := by
  have h := congrArg (coeff 7) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at h ⊢ <;> linarith

theorem hs9 : coeff 9 S = (-18570 : ℚ) := by
  have h := congrArg (coeff 8) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8] at h ⊢ <;> linarith

theorem hs10 : coeff 10 S = (-79174 : ℚ) := by
  have h := congrArg (coeff 9) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9] at h ⊢ <;> linarith

theorem hs11 : coeff 11 S = (-342738 : ℚ) := by
  have h := congrArg (coeff 10) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10] at h ⊢ <;> linarith

theorem hf0 : coeff 0 F = (0 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (0 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (0 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (0 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (0 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (0 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (1 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (8 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem hf7 : coeff 7 F = (48 : ℚ) := by
  have h := congrArg (coeff 7) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf0c] at h ⊢ <;> linarith

theorem hf8 : coeff 8 F = (261 : ℚ) := by
  have h := congrArg (coeff 8) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf0c] at h ⊢ <;> linarith

theorem hf9 : coeff 9 F = (1358 : ℚ) := by
  have h := congrArg (coeff 9) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf0c] at h ⊢ <;> linarith

theorem hf10 : coeff 10 F = (6907 : ℚ) := by
  have h := congrArg (coeff 10) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf0c] at h ⊢ <;> linarith

theorem hf11 : coeff 11 F = (34684 : ℚ) := by
  have h := congrArg (coeff 11) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (0 : ℚ) := by rw [a_eq]; exact hf2

theorem ha1 : a 1 = (0 : ℚ) := by rw [a_eq]; exact hf3

theorem ha2 : a 2 = (0 : ℚ) := by rw [a_eq]; exact hf4

theorem ha3 : a 3 = (1 : ℚ) := by rw [a_eq]; exact hf5

theorem ha4 : a 4 = (8 : ℚ) := by rw [a_eq]; exact hf6

theorem ha5 : a 5 = (48 : ℚ) := by rw [a_eq]; exact hf7

theorem ha6 : a 6 = (261 : ℚ) := by rw [a_eq]; exact hf8

theorem ha7 : a 7 = (1358 : ℚ) := by rw [a_eq]; exact hf9

theorem ha8 : a 8 = (6907 : ℚ) := by rw [a_eq]; exact hf10

theorem ha9 : a 9 = (34684 : ℚ) := by rw [a_eq]; exact hf11

noncomputable def Mv (n : ℕ) : ℚ := (6 * (n : ℚ) ^ 3 - 52 * (n : ℚ) ^ 2 + 62 * (n : ℚ) + 120) * a n
      + (-39 * (n : ℚ) ^ 3 + 362 * (n : ℚ) ^ 2 - 739 * (n : ℚ) + 300) * a (n - 1)
      + (48 * (n : ℚ) ^ 3 - 488 * (n : ℚ) ^ 2 + 1384 * (n : ℚ) - 1200) * a (n - 2)
      + (-15 * (n : ℚ) ^ 3 + 160 * (n : ℚ) ^ 2 - 515 * (n : ℚ) + 510) * a (n - 3)

theorem base3 : Mv 3 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]

theorem base4 : Mv 4 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]

theorem base5 : Mv 5 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]

theorem base6 : Mv 6 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]

theorem base7 : Mv 7 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]

theorem base8 : Mv 8 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]

theorem base9 : Mv 9 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]

theorem certQ (k : ℕ) : ((-246668 / 14787 : ℚ) + (67807 / 9858 : ℚ) * ((k : ℚ) + 6) ^ 1) * Mv (k + 6) + ((7499033 / 73935 : ℚ) + (-733163 / 24645 : ℚ) * ((k : ℚ) + 6) ^ 1) * Mv (k + 7) + ((-19798432 / 123225 : ℚ) + (3141503 / 82150 : ℚ) * ((k : ℚ) + 6) ^ 1) * Mv (k + 8) + ((22681453 / 369675 : ℚ) + (-1624099 / 123225 : ℚ) * ((k : ℚ) + 6) ^ 1) * Mv (k + 9) + ((-526588 / 73935 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 6) ^ 1) * Mv (k + 10) = 0 := by
  unfold Mv
  rw [show k + 6 - 1 = k + 5 from by omega, show k + 6 - 2 = k + 4 from by omega, show k + 6 - 3 = k + 3 from by omega, show k + 7 - 1 = k + 6 from by omega, show k + 7 - 2 = k + 5 from by omega, show k + 7 - 3 = k + 4 from by omega, show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 8 - 3 = k + 5 from by omega, show k + 9 - 1 = k + 8 from by omega, show k + 9 - 2 = k + 7 from by omega, show k + 9 - 3 = k + 6 from by omega, show k + 10 - 1 = k + 9 from by omega, show k + 10 - 2 = k + 8 from by omega, show k + 10 - 3 = k + 7 from by omega]
  simp only [a_eq]
  have r1_50 := rel1 (k + 2)
  have r1_51 := rel1 (k + 3)
  have r1_52 := rel1 (k + 4)
  have r1_53 := rel1 (k + 5)
  have r1_54 := rel1 (k + 6)
  have r2_47 := rel2 (k + 3)
  have r2_48 := rel2 (k + 4)
  have r2_49 := rel2 (k + 5)
  have r2_50 := rel2 (k + 6)
  have r2_51 := rel2 (k + 7)
  have r2_52 := rel2 (k + 8)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_50 r1_51 r1_52 r1_53 r1_54 r2_47 r2_48 r2_49 r2_50 r2_51 r2_52 ⊢
  push_cast at r1_50 r1_51 r1_52 r1_53 r1_54 r2_47 r2_48 r2_49 r2_50 r2_51 r2_52 ⊢
  linear_combination ((4193356 / 4929 : ℚ) + (-35781275 / 29574 : ℚ) * ((k : ℚ) + 6) ^ 1 + (36739115 / 59148 : ℚ) * ((k : ℚ) + 6) ^ 2 + (-221930 / 1643 : ℚ) * ((k : ℚ) + 6) ^ 3 + (67807 / 6572 : ℚ) * ((k : ℚ) + 6) ^ 4) * r1_50 + ((11194166 / 73935 : ℚ) + (133573613 / 147870 : ℚ) * ((k : ℚ) + 6) ^ 1 + (-306867679 / 295740 : ℚ) * ((k : ℚ) + 6) ^ 2 + (2815033 / 8215 : ℚ) * ((k : ℚ) + 6) ^ 3 + (-1127291 / 32860 : ℚ) * ((k : ℚ) + 6) ^ 4) * r1_51 + ((-5186138 / 14787 : ℚ) + (678911207 / 739350 : ℚ) * ((k : ℚ) + 6) ^ 1 + (117770447 / 492900 : ℚ) * ((k : ℚ) + 6) ^ 2 + (-10079076 / 41075 : ℚ) * ((k : ℚ) + 6) ^ 3 + (5483229 / 164300 : ℚ) * ((k : ℚ) + 6) ^ 4) * r1_52 + ((-2106352 / 14787 : ℚ) + (-406211881 / 739350 : ℚ) * ((k : ℚ) + 6) ^ 1 + (191275991 / 1478700 : ℚ) * ((k : ℚ) + 6) ^ 2 + (1960327 / 41075 : ℚ) * ((k : ℚ) + 6) ^ 3 + (-1706249 / 164300 : ℚ) * ((k : ℚ) + 6) ^ 4) * r1_53 + ((1053176 / 14787 : ℚ) + (1119517 / 24645 : ℚ) * ((k : ℚ) + 6) ^ 1 + (-425951 / 14787 : ℚ) * ((k : ℚ) + 6) ^ 2 + (-16499 / 8215 : ℚ) * ((k : ℚ) + 6) ^ 3 + (1 : ℚ) * ((k : ℚ) + 6) ^ 4) * r1_54 + ((2096678 / 24645 : ℚ) + (-9131521 / 98580 : ℚ) * ((k : ℚ) + 6) ^ 1 + (2052897 / 65720 : ℚ) * ((k : ℚ) + 6) ^ 2 + (-203421 / 65720 : ℚ) * ((k : ℚ) + 6) ^ 3) * r2_47 + ((-18170021 / 49290 : ℚ) + (1426078451 / 2957400 : ℚ) * ((k : ℚ) + 6) ^ 1 + (-56675361 / 328600 : ℚ) * ((k : ℚ) + 6) ^ 2 + (1472683 / 82150 : ℚ) * ((k : ℚ) + 6) ^ 3) * r2_48 + ((65489131 / 147870 : ℚ) + (-2535874813 / 2957400 : ℚ) * ((k : ℚ) + 6) ^ 1 + (111130841 / 328600 : ℚ) * ((k : ℚ) + 6) ^ 2 + (-1518403 / 41075 : ℚ) * ((k : ℚ) + 6) ^ 3) * r2_49 + ((-327571 / 4929 : ℚ) + (1977013 / 3286 : ℚ) * ((k : ℚ) + 6) ^ 1 + (-339297 / 1240 : ℚ) * ((k : ℚ) + 6) ^ 2 + (10410309 / 328600 : ℚ) * ((k : ℚ) + 6) ^ 3) * r2_50 + ((-1448117 / 24645 : ℚ) + (-193736183 / 1478700 : ℚ) * ((k : ℚ) + 6) ^ 1 + (6347007 / 82150 : ℚ) * ((k : ℚ) + 6) ^ 2 + (-1624099 / 164300 : ℚ) * ((k : ℚ) + 6) ^ 3) * r2_51 + ((1053176 / 73935 : ℚ) + (92215 / 14787 : ℚ) * ((k : ℚ) + 6) ^ 1 + (-57574 / 8215 : ℚ) * ((k : ℚ) + 6) ^ 2 + (1 : ℚ) * ((k : ℚ) + 6) ^ 3) * r2_52

theorem Mv_zero : ∀ n : ℕ, 3 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 10
    · interval_cases n
      · exact base3
      · exact base4
      · exact base5
      · exact base6
      · exact base7
      · exact base8
      · exact base9
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 6) = 0 := ih _ (by omega) (by omega)
      have h1 : Mv (k + 7) = 0 := ih _ (by omega) (by omega)
      have h2 : Mv (k + 8) = 0 := ih _ (by omega) (by omega)
      have h3 : Mv (k + 9) = 0 := ih _ (by omega) (by omega)
      have hq : ((-526588 / 73935 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 6) ^ 1) ≠ 0 := by
        have e : ((-526588 / 73935 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 6) ^ 1) = (64892 / 73935 : ℚ) + (4 / 3 : ℚ) * (k : ℚ) ^ 1 := by ring
        rw [e]
        positivity
      have hm : ((-526588 / 73935 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 6) ^ 1) * Mv (k + 10) = 0 := by linear_combination hc - ((-246668 / 14787 : ℚ) + (67807 / 9858 : ℚ) * ((k : ℚ) + 6) ^ 1) * h0 - ((7499033 / 73935 : ℚ) + (-733163 / 24645 : ℚ) * ((k : ℚ) + 6) ^ 1) * h1 - ((-19798432 / 123225 : ℚ) + (3141503 / 82150 : ℚ) * ((k : ℚ) + 6) ^ 1) * h2 - ((22681453 / 369675 : ℚ) + (-1624099 / 123225 : ℚ) * ((k : ℚ) + 6) ^ 1) * h3
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 3 ≤ n → (6 * (n : ℚ) ^ 3 - 52 * (n : ℚ) ^ 2 + 62 * (n : ℚ) + 120) * a n
      + (-39 * (n : ℚ) ^ 3 + 362 * (n : ℚ) ^ 2 - 739 * (n : ℚ) + 300) * a (n - 1)
      + (48 * (n : ℚ) ^ 3 - 488 * (n : ℚ) ^ 2 + 1384 * (n : ℚ) - 1200) * a (n - 2)
      + (-15 * (n : ℚ) ^ 3 + 160 * (n : ℚ) ^ 2 - 515 * (n : ℚ) + 510) * a (n - 3) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a128734

theorem OMA.solution : type_of% @OMA.S_oeis_a128734.main := OMA.P_oeis_a128734.main'
