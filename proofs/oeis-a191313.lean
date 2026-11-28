import OMAStatements.S_oeis_a191313
import Mathlib

-- Problem: A191313: Sum of the abscissae of the first returns to the horizontal axis (assumed to be 0 if there are no such returns) in all dispersed Dyck paths of length n (i.e., Motzkin paths of length n with no (1,0) steps at positive heights).
-- Upstream: formal-conjectures statements/oeis-a191313.lean (declaration OMA.S_oeis_a191313.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a191313

open OMA.S_oeis_a191313 PowerSeries

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

theorem hRC : R = C (1 : ℚ) + C (-4 : ℚ) * X ^ 2 := by
  simp only [R, map_one, map_neg, map_ofNat]
  ring

theorem hDR : d⁄dX ℚ R = C (-8 : ℚ) * X ^ 1 := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  push_cast
  ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-8 : ℚ) * X ^ 2 * d⁄dX ℚ S - (C (-8 : ℚ) * X ^ 1 * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 3) S * ((m : ℚ) + 3)) + (-8 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-8 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 2)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((-1 + 4 * X + X ^ 2 - 16 * X ^ 3 + 12 * X ^ 4 + (1 - 4 * X + 5 * X ^ 2 - 2 * X ^ 3) * S) * (2 - 10 * X + 10 * X ^ 2 + 26 * X ^ 3 - 68 * X ^ 4 + 56 * X ^ 5 - 16 * X ^ 6 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff n F := rfl

theorem hF : F * (2 - 10 * X + 10 * X ^ 2 + 26 * X ^ 3 - 68 * X ^ 4 + 56 * X ^ 5 - 16 * X ^ 6 : ℚ⟦X⟧) = -1 + 4 * X + X ^ 2 - 16 * X ^ 3 + 12 * X ^ 4 + (1 - 4 * X + 5 * X ^ 2 - 2 * X ^ 3) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (2 - 10 * X + 10 * X ^ 2 + 26 * X ^ 3 - 68 * X ^ 4 + 56 * X ^ 5 - 16 * X ^ 6 : ℚ⟦X⟧) = C (2 : ℚ) + C (-10 : ℚ) * X ^ 1 + C (10 : ℚ) * X ^ 2 + C (26 : ℚ) * X ^ 3 + C (-68 : ℚ) * X ^ 4 + C (56 : ℚ) * X ^ 5 + C (-16 : ℚ) * X ^ 6 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (2 : ℚ) * F + C (-10 : ℚ) * X ^ 1 * F + C (10 : ℚ) * X ^ 2 * F + C (26 : ℚ) * X ^ 3 * F + C (-68 : ℚ) * X ^ 4 * F + C (56 : ℚ) * X ^ 5 * F + C (-16 : ℚ) * X ^ 6 * F - (C (1 : ℚ) * S + C (-4 : ℚ) * X ^ 1 * S + C (5 : ℚ) * X ^ 2 * S + C (-2 : ℚ) * X ^ 3 * S) - (C (-1 : ℚ) + C (4 : ℚ) * X ^ 1 + C (1 : ℚ) * X ^ 2 + C (-16 : ℚ) * X ^ 3 + C (12 : ℚ) * X ^ 4) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 6) F + (-10 : ℚ) * coeff (m + 5) F + (10 : ℚ) * coeff (m + 4) F + (26 : ℚ) * coeff (m + 3) F + (-68 : ℚ) * coeff (m + 2) F + (56 : ℚ) * coeff (m + 1) F + (-16 : ℚ) * coeff (m) F - ((1 : ℚ) * coeff (m + 6) S + (-4 : ℚ) * coeff (m + 5) S + (5 : ℚ) * coeff (m + 4) S + (-2 : ℚ) * coeff (m + 3) S) = 0 := by
  have h := congrArg (coeff (m + 6)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 6 - 1 = m + 5 from by omega, show m + 6 - 2 = m + 4 from by omega, show m + 6 - 3 = m + 3 from by omega, show m + 6 - 4 = m + 2 from by omega, show m + 6 - 5 = m + 1 from by omega, show m + 6 - 6 = m from by omega] at h
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

theorem hs1 : coeff 1 S = (0 : ℚ) := by
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

theorem hs3 : coeff 3 S = (0 : ℚ) := by
  have h := congrArg (coeff 2) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2] at h ⊢ <;> linarith

theorem hs4 : coeff 4 S = (-2 : ℚ) := by
  have h := congrArg (coeff 3) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3] at h ⊢ <;> linarith

theorem hs5 : coeff 5 S = (0 : ℚ) := by
  have h := congrArg (coeff 4) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4] at h ⊢ <;> linarith

theorem hs6 : coeff 6 S = (-4 : ℚ) := by
  have h := congrArg (coeff 5) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5] at h ⊢ <;> linarith

theorem hs7 : coeff 7 S = (0 : ℚ) := by
  have h := congrArg (coeff 6) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at h ⊢ <;> linarith

theorem hs8 : coeff 8 S = (-10 : ℚ) := by
  have h := congrArg (coeff 7) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at h ⊢ <;> linarith

theorem hf0 : coeff 0 F = (0 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (0 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (0 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (2 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (5 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (15 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (30 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (71 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem hf7 : coeff 7 F = (134 : ℚ) := by
  have h := congrArg (coeff 7) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf0c] at h ⊢ <;> linarith

theorem hf8 : coeff 8 F = (296 : ℚ) := by
  have h := congrArg (coeff 8) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (0 : ℚ) := by rw [a_eq]; exact hf0

theorem ha1 : a 1 = (0 : ℚ) := by rw [a_eq]; exact hf1

theorem ha2 : a 2 = (2 : ℚ) := by rw [a_eq]; exact hf2

theorem ha3 : a 3 = (5 : ℚ) := by rw [a_eq]; exact hf3

theorem ha4 : a 4 = (15 : ℚ) := by rw [a_eq]; exact hf4

theorem ha5 : a 5 = (30 : ℚ) := by rw [a_eq]; exact hf5

theorem ha6 : a 6 = (71 : ℚ) := by rw [a_eq]; exact hf6

theorem ha7 : a 7 = (134 : ℚ) := by rw [a_eq]; exact hf7

theorem ha8 : a 8 = (296 : ℚ) := by rw [a_eq]; exact hf8

noncomputable def Mv (n : ℕ) : ℚ := (3 * (n : ℚ) ^ 2 - 13 * (n : ℚ)) * a n + (-12 * (n : ℚ) ^ 2 + 58 * (n : ℚ) - 36) * a (n - 1)
      + (3 * (n : ℚ) ^ 2 - 13 * (n : ℚ) + 24) * a (n - 2)
      + (42 * (n : ℚ) ^ 2 - 248 * (n : ℚ) + 300) * a (n - 3)
      + (-60 * (n : ℚ) ^ 2 + 368 * (n : ℚ) - 528) * a (n - 4)
      + (24 * (n : ℚ) ^ 2 - 152 * (n : ℚ) + 240) * a (n - 5)

theorem base5 : Mv 5 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]

theorem base6 : Mv 6 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]

theorem base7 : Mv 7 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]

theorem base8 : Mv 8 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]

theorem certQ (k : ℕ) : ((326816 / 17595 : ℚ) + (-103784 / 5865 : ℚ) * ((k : ℚ) + 5) ^ 1 + (4728 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 2) * Mv (k + 5) + ((-512608 / 17595 : ℚ) + (163432 / 5865 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-4728 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 2) * Mv (k + 6) + ((-22548 / 1955 : ℚ) + (586 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-1182 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 2) * Mv (k + 7) + ((344932 / 17595 : ℚ) + (-9590 / 1173 : ℚ) * ((k : ℚ) + 5) ^ 1 + (1182 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 2) * Mv (k + 8) + ((-9688 / 3519 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 5) ^ 1) * Mv (k + 9) = 0 := by
  unfold Mv
  rw [show k + 5 - 1 = k + 4 from by omega, show k + 5 - 2 = k + 3 from by omega, show k + 5 - 3 = k + 2 from by omega, show k + 5 - 4 = k + 1 from by omega, show k + 5 - 5 = k from by omega, show k + 6 - 1 = k + 5 from by omega, show k + 6 - 2 = k + 4 from by omega, show k + 6 - 3 = k + 3 from by omega, show k + 6 - 4 = k + 2 from by omega, show k + 6 - 5 = k + 1 from by omega, show k + 7 - 1 = k + 6 from by omega, show k + 7 - 2 = k + 5 from by omega, show k + 7 - 3 = k + 4 from by omega, show k + 7 - 4 = k + 3 from by omega, show k + 7 - 5 = k + 2 from by omega, show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 8 - 3 = k + 5 from by omega, show k + 8 - 4 = k + 4 from by omega, show k + 8 - 5 = k + 3 from by omega, show k + 9 - 1 = k + 8 from by omega, show k + 9 - 2 = k + 7 from by omega, show k + 9 - 3 = k + 6 from by omega, show k + 9 - 4 = k + 5 from by omega, show k + 9 - 5 = k + 4 from by omega]
  simp only [a_eq]
  have r1_51 := rel1 (k)
  have r1_52 := rel1 (k + 1)
  have r1_53 := rel1 (k + 2)
  have r1_54 := rel1 (k + 3)
  have r2_49 := rel2 (k + 2)
  have r2_50 := rel2 (k + 3)
  have r2_51 := rel2 (k + 4)
  have r2_52 := rel2 (k + 5)
  have r2_53 := rel2 (k + 6)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_51 r1_52 r1_53 r1_54 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  push_cast at r1_51 r1_52 r1_53 r1_54 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  linear_combination ((-326816 / 1173 : ℚ) + (7775032 / 17595 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-1362116 / 5865 : ℚ) * ((k : ℚ) + 5) ^ 2 + (96808 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 3 + (-7092 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 4) * r1_51 + ((-121072 / 765 : ℚ) + (2657204 / 17595 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-3734 / 255 : ℚ) * ((k : ℚ) + 5) ^ 2 + (-12094 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 3) * r1_52 + ((-1682072 / 17595 : ℚ) + (225202 / 3519 : ℚ) * ((k : ℚ) + 5) ^ 1 + (14713 / 1173 : ℚ) * ((k : ℚ) + 5) ^ 2 + (-3422 / 391 : ℚ) * ((k : ℚ) + 5) ^ 3 + (1773 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 4) * r1_53 + ((19376 / 3519 : ℚ) + (-62668 / 3519 : ℚ) * ((k : ℚ) + 5) ^ 1 + (3758 / 1173 : ℚ) * ((k : ℚ) + 5) ^ 2 + (2 : ℚ) * ((k : ℚ) + 5) ^ 3) * r1_54 + ((81704 / 3519 : ℚ) + (-170582 / 5865 : ℚ) * ((k : ℚ) + 5) ^ 1 + (821 / 85 : ℚ) * ((k : ℚ) + 5) ^ 2 + (-1773 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 3) * r2_49 + ((-1183868 / 17595 : ℚ) + (501871 / 5865 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-6431 / 230 : ℚ) * ((k : ℚ) + 5) ^ 2 + (1773 / 782 : ℚ) * ((k : ℚ) + 5) ^ 3) * r2_50 + ((125692 / 1955 : ℚ) + (-164352 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 1 + (10572 / 391 : ℚ) * ((k : ℚ) + 5) ^ 2 + (-3546 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 3) * r2_51 + ((-344932 / 17595 : ℚ) + (170513 / 5865 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-38069 / 3910 : ℚ) * ((k : ℚ) + 5) ^ 2 + (1773 / 3910 : ℚ) * ((k : ℚ) + 5) ^ 3) * r2_52 + ((2422 / 3519 : ℚ) + (-2813 / 1173 : ℚ) * ((k : ℚ) + 5) ^ 1 + (1 : ℚ) * ((k : ℚ) + 5) ^ 2) * r2_53

theorem Mv_zero : ∀ n : ℕ, 5 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 9
    · interval_cases n
      · exact base5
      · exact base6
      · exact base7
      · exact base8
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 5) = 0 := ih _ (by omega) (by omega)
      have h1 : Mv (k + 6) = 0 := ih _ (by omega) (by omega)
      have h2 : Mv (k + 7) = 0 := ih _ (by omega) (by omega)
      have h3 : Mv (k + 8) = 0 := ih _ (by omega) (by omega)
      have hq : ((-9688 / 3519 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 5) ^ 1) ≠ 0 := by
        have e : ((-9688 / 3519 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 5) ^ 1) = (13772 / 3519 : ℚ) + (4 / 3 : ℚ) * (k : ℚ) ^ 1 := by ring
        rw [e]
        positivity
      have hm : ((-9688 / 3519 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 5) ^ 1) * Mv (k + 9) = 0 := by linear_combination hc - ((326816 / 17595 : ℚ) + (-103784 / 5865 : ℚ) * ((k : ℚ) + 5) ^ 1 + (4728 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 2) * h0 - ((-512608 / 17595 : ℚ) + (163432 / 5865 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-4728 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 2) * h1 - ((-22548 / 1955 : ℚ) + (586 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-1182 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 2) * h2 - ((344932 / 17595 : ℚ) + (-9590 / 1173 : ℚ) * ((k : ℚ) + 5) ^ 1 + (1182 / 1955 : ℚ) * ((k : ℚ) + 5) ^ 2) * h3
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 5 ≤ n → (3 * (n : ℚ) ^ 2 - 13 * (n : ℚ)) * a n + (-12 * (n : ℚ) ^ 2 + 58 * (n : ℚ) - 36) * a (n - 1)
      + (3 * (n : ℚ) ^ 2 - 13 * (n : ℚ) + 24) * a (n - 2)
      + (42 * (n : ℚ) ^ 2 - 248 * (n : ℚ) + 300) * a (n - 3)
      + (-60 * (n : ℚ) ^ 2 + 368 * (n : ℚ) - 528) * a (n - 4)
      + (24 * (n : ℚ) ^ 2 - 152 * (n : ℚ) + 240) * a (n - 5) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a191313

theorem OMA.solution : type_of% @OMA.S_oeis_a191313.main := OMA.P_oeis_a191313.main'
