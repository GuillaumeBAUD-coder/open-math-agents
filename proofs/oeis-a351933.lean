import OMAStatements.S_oeis_a351933
import Mathlib

-- Problem: A351933, conjectured recurrence for a(n) = n! [x^n] exp(x / (1 - x^2/2)).
-- Upstream: formal-conjectures statements/oeis-a351933.lean (declaration OMA.S_oeis_a351933.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the e.g.f. as defined).
-- Proof idea: W = exp(U) satisfies q^2 W' = (p'q - pq') W for U = p/q (rel2). Writing
-- a(n-i) = (n-i)! w(n-i) and factoring out k!, the recurrence for n >= 5 is an explicit polynomial
-- combination of shifted instances of rel2; the case n = 4 is checked from exact values.

namespace OMA.P_oeis_a351933

open OMA.S_oeis_a351933 PowerSeries

theorem hU : HasSubst U := HasSubst.of_constantCoeff_zero' (by simp [U])

theorem dexp : d⁄dX ℚ (PowerSeries.exp ℚ) = PowerSeries.exp ℚ := by
  ext n
  rw [coeff_derivative, coeff_exp, coeff_exp, Nat.factorial_succ]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  push_cast
  have h : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem dW : d⁄dX ℚ W = W * d⁄dX ℚ U := by
  unfold W
  rw [derivative_subst hU, dexp]

theorem hdp : d⁄dX ℚ (2 * X : ℚ⟦X⟧) = 2 := by
  rw [show (2 * X : ℚ⟦X⟧) = C (2 : ℚ) * X ^ 1 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, zero_add, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  try push_cast
  try ring

theorem hdq : d⁄dX ℚ (2 - X ^ 2 : ℚ⟦X⟧) = -2 * X := by
  rw [show (2 - X ^ 2 : ℚ⟦X⟧) = C (2 : ℚ) + C (-1 : ℚ) * X ^ 2 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, zero_add, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  try push_cast
  try ring

theorem ode : (4 - 4 * X ^ 2 + X ^ 4 : ℚ⟦X⟧) * d⁄dX ℚ W = (4 + 2 * X ^ 2) * W := by
  have hq : (2 - X ^ 2 : ℚ⟦X⟧) * (2 - X ^ 2 : ℚ⟦X⟧)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by
    rw [show (2 - X ^ 2 : ℚ⟦X⟧) = C (2 : ℚ) + C (-1 : ℚ) * X ^ 2 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp)
  rw [dW]
  unfold U
  rw [Derivation.leibniz, derivative_inv', smul_eq_mul, smul_eq_mul, hdp, hdq]
  linear_combination (W * (-(2 * X) * (-2 * X) * ((2 - X ^ 2 : ℚ⟦X⟧) * (2 - X ^ 2 : ℚ⟦X⟧)⁻¹ + 1) + (2) * (2 - X ^ 2))) * hq

theorem E2 : C (4 : ℚ) * d⁄dX ℚ W + C (-4 : ℚ) * X ^ 2 * d⁄dX ℚ W + C (1 : ℚ) * X ^ 4 * d⁄dX ℚ W - (C (4 : ℚ) * W + C (2 : ℚ) * X ^ 2 * W) = 0 := by
  have h := ode
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem cx (c : ℚ) (j n : ℕ) (f : ℚ⟦X⟧) (h : j ≤ n) :
    coeff n (C c * X ^ j * f) = c * coeff (n - j) f := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos h]

theorem cx0 (c : ℚ) (n : ℕ) (f : ℚ⟦X⟧) : coeff n (C c * f) = c * coeff n f := coeff_C_mul _ _ _

theorem cc (c : ℚ) (j n : ℕ) (h : n ≠ j) : coeff n (C c * X ^ j) = 0 := by
  rw [coeff_C_mul_X_pow, if_neg h]

theorem cc0 (c : ℚ) (n : ℕ) (h : n ≠ 0) : coeff n (C c : ℚ⟦X⟧) = 0 := by
  rw [coeff_C, if_neg h]

theorem rel2 (m : ℕ) : (4 : ℚ) * (coeff (m + 5) W * ((m : ℚ) + 5)) + (-4 : ℚ) * (coeff (m + 3) W * ((m : ℚ) + 3)) + (1 : ℚ) * (coeff (m + 1) W * ((m : ℚ) + 1)) - ((4 : ℚ) * coeff (m + 4) W + (2 : ℚ) * coeff (m + 2) W) = 0 := by
  have h := congrArg (coeff (m + 4)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 4 - 2 = m + 2 from by omega, show m + 4 - 4 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := (((1) * W + (0)) * (1 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = (n.factorial : ℚ) * coeff n F := rfl

theorem hF : F * (1 : ℚ⟦X⟧) = (1) * W + (0) := by
  have h1 : (1 : ℚ⟦X⟧)⁻¹ = 1 := by
    have h := PowerSeries.mul_inv_cancel (1 : ℚ⟦X⟧) (by simp)
    rwa [one_mul] at h
  unfold F
  try rw [h1]
  ring

theorem E1 : C (1 : ℚ) * F - (C (1 : ℚ) * W) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (1 : ℚ) * coeff (m) F - ((1 : ℚ) * coeff (m) W) = 0 := by
  have h := congrArg (coeff (m)) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cc, cc0] at h
  try simp only [cx0, sub_zero, add_zero, zero_add] at h
  skip
  linear_combination h

theorem cz (c : ℚ) (j n : ℕ) (f : ℚ⟦X⟧) (h : n < j) : coeff n (C c * X ^ j * f) = 0 := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_neg (by omega), mul_zero]

theorem ccj (c : ℚ) (j n : ℕ) (h : n = j) : coeff n (C c * X ^ j) = c := by
  rw [coeff_C_mul_X_pow, if_pos h]

theorem cc0' (c : ℚ) : coeff 0 (C c : ℚ⟦X⟧) = c := by rw [coeff_C, if_pos rfl]

theorem W_const : constantCoeff W = 1 := by
  have h0 : constantCoeff (PowerSeries.exp ℚ - 1) = 0 := by simp
  have hc : constantCoeff U = 0 := by simp [U]
  have h1 := constantCoeff_subst_eq_zero (a := (U : ℚ⟦X⟧)) hc _ h0
  have h2 : (PowerSeries.exp ℚ - 1).subst U = W - 1 := by
    unfold W
    rw [← coe_substAlgHom hU, map_sub, map_one]
  rw [h2] at h1
  have h3 : constantCoeff (W - 1) = 0 := h1
  rw [map_sub, map_one, sub_eq_zero] at h3
  exact h3

theorem hw0 : coeff 0 W = 1 := by rw [coeff_zero_eq_constantCoeff_apply, W_const]

theorem hw1 : coeff 1 W = (1 : ℚ) := by
  have h := congrArg (coeff 0) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [W_const, hw0] at h ⊢ <;> linarith

theorem hw2 : coeff 2 W = (1 / 2 : ℚ) := by
  have h := congrArg (coeff 1) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [W_const, hw0, hw1] at h ⊢ <;> linarith

theorem hw3 : coeff 3 W = (2 / 3 : ℚ) := by
  have h := congrArg (coeff 2) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [W_const, hw0, hw1, hw2] at h ⊢ <;> linarith

theorem hw4 : coeff 4 W = (13 / 24 : ℚ) := by
  have h := congrArg (coeff 3) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [W_const, hw0, hw1, hw2, hw3] at h ⊢ <;> linarith

theorem hf0 : coeff 0 F = (1 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [W_const, hw0, hw1, hw2, hw3, hw4] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (1 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (1 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [W_const, hw0, hw1, hw2, hw3, hw4, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (1 / 2 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [W_const, hw0, hw1, hw2, hw3, hw4, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (2 / 3 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [W_const, hw0, hw1, hw2, hw3, hw4, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (13 / 24 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [W_const, hw0, hw1, hw2, hw3, hw4, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (1 : ℚ) := by rw [a_eq, hf0]; norm_num [Nat.factorial]

theorem ha1 : a 1 = (1 : ℚ) := by rw [a_eq, hf1]; norm_num [Nat.factorial]

theorem ha2 : a 2 = (1 : ℚ) := by rw [a_eq, hf2]; norm_num [Nat.factorial]

theorem ha3 : a 3 = (4 : ℚ) := by rw [a_eq, hf3]; norm_num [Nat.factorial]

theorem ha4 : a 4 = (13 : ℚ) := by rw [a_eq, hf4]; norm_num [Nat.factorial]

theorem main' : ∀ n : ℕ, 4 ≤ n →
    (4) * a n + (-4) * a (n - 1) + (-4 * (n : ℚ) ^ 2 + 12 * (n : ℚ) - 8) * a (n - 2)
      + (-2 * (n : ℚ) ^ 2 + 6 * (n : ℚ) - 4) * a (n - 3)
      + ((n : ℚ) ^ 4 - 10 * (n : ℚ) ^ 3 + 35 * (n : ℚ) ^ 2 - 50 * (n : ℚ) + 24) * a (n - 4) = 0 := by
  intro n hn
  by_cases hlt : n < 5
  · interval_cases n
    · norm_num [ha0, ha1, ha2, ha3, ha4]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rw [show k + 5 - 1 = k + 4 from by omega, show k + 5 - 2 = k + 3 from by omega, show k + 5 - 3 = k + 2 from by omega, show k + 5 - 4 = k + 1 from by omega]
  simp only [a_eq]
  have r1_46 := rel1 (k + 1)
  have r1_47 := rel1 (k + 2)
  have r1_48 := rel1 (k + 3)
  have r1_49 := rel1 (k + 4)
  have r1_50 := rel1 (k + 5)
  have r2_49 := rel2 (k)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_46 r1_47 r1_48 r1_49 r1_50 r2_49 ⊢
  simp only [Nat.factorial_succ]
  push_cast at r1_46 r1_47 r1_48 r1_49 r1_50 r2_49 ⊢
  linear_combination (k.factorial : ℚ) * (((-96 : ℚ) + (224 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-190 : ℚ) * ((k : ℚ) + 5) ^ 2 + (75 : ℚ) * ((k : ℚ) + 5) ^ 3 + (-14 : ℚ) * ((k : ℚ) + 5) ^ 4 + (1 : ℚ) * ((k : ℚ) + 5) ^ 5) * r1_46 + ((-48 : ℚ) + (100 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-70 : ℚ) * ((k : ℚ) + 5) ^ 2 + (20 : ℚ) * ((k : ℚ) + 5) ^ 3 + (-2 : ℚ) * ((k : ℚ) + 5) ^ 4) * r1_47 + ((192 : ℚ) + (-496 : ℚ) * ((k : ℚ) + 5) ^ 1 + (480 : ℚ) * ((k : ℚ) + 5) ^ 2 + (-220 : ℚ) * ((k : ℚ) + 5) ^ 3 + (48 : ℚ) * ((k : ℚ) + 5) ^ 4 + (-4 : ℚ) * ((k : ℚ) + 5) ^ 5) * r1_48 + ((-96 : ℚ) + (200 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-140 : ℚ) * ((k : ℚ) + 5) ^ 2 + (40 : ℚ) * ((k : ℚ) + 5) ^ 3 + (-4 : ℚ) * ((k : ℚ) + 5) ^ 4) * r1_49 + ((96 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-200 : ℚ) * ((k : ℚ) + 5) ^ 2 + (140 : ℚ) * ((k : ℚ) + 5) ^ 3 + (-40 : ℚ) * ((k : ℚ) + 5) ^ 4 + (4 : ℚ) * ((k : ℚ) + 5) ^ 5) * r1_50 + ((24 : ℚ) + (-50 : ℚ) * ((k : ℚ) + 5) ^ 1 + (35 : ℚ) * ((k : ℚ) + 5) ^ 2 + (-10 : ℚ) * ((k : ℚ) + 5) ^ 3 + (1 : ℚ) * ((k : ℚ) + 5) ^ 4) * r2_49)

end OMA.P_oeis_a351933

theorem OMA.solution : type_of% @OMA.S_oeis_a351933.main := OMA.P_oeis_a351933.main'
