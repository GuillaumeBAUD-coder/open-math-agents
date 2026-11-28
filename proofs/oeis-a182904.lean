import OMAStatements.S_oeis_a182904
import Mathlib

namespace OMA.P182904

open PowerSeries OMA.S_oeis_a182904

lemma hR0 : constantCoeff (R - 1) = 0 := by
  simp [R]

lemma hsub : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' hR0

lemma hone : (1 : PowerSeries ℚ).subst (R - 1) = 1 := by
  rw [← coe_substAlgHom hsub]
  exact map_one _

lemma hS : S ^ 2 = R := by
  have h2 : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = 1 + X := by
    rw [pow_two, ← PowerSeries.binomialSeries_add]
    have h := PowerSeries.binomialSeries_nat (R := ℚ) (A := ℚ) 1
    norm_num at h ⊢
    exact h
  unfold S
  rw [← subst_pow hsub, h2, subst_add hsub, subst_X hsub, hone]
  ring

lemma hS0 : constantCoeff S = 1 := by
  have e : PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) = 1 + (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - 1) := by ring
  have hz : constantCoeff ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - 1).subst (R - 1)) = 0 :=
    constantCoeff_subst_eq_zero hR0 _ (by simp)
  unfold S
  rw [e, subst_add hsub, hone, map_add, hz]
  simp

/-- The first-order differential equation satisfied by a series of the form (P + Q sqrt(Δ)) / D. -/
lemma ode (S Δ D P Q G : PowerSeries ℚ) (hS : S ^ 2 = Δ) (hG : D * G = P + Q * S) :
    2 * Δ * Q * D * derivative ℚ G
      + (2 * Δ * Q * derivative ℚ D - (2 * Δ * derivative ℚ Q + Q * derivative ℚ Δ) * D) * G
    = 2 * Δ * Q * derivative ℚ P - (2 * Δ * derivative ℚ Q + Q * derivative ℚ Δ) * P := by
  have hS' := congrArg (derivative ℚ) hS
  have hG' := congrArg (derivative ℚ) hG
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hS' hG'
  push_cast at hS' hG'
  linear_combination (2 * Δ * Q) * hG' - (2 * Δ * derivative ℚ Q + Q * derivative ℚ Δ) * hG
    + (Q ^ 2 * S) * hS' - (2 * Q ^ 2 * derivative ℚ S) * hS

lemma dOfNat (m : ℕ) [m.AtLeastTwo] : derivative ℚ (ofNat(m) : PowerSeries ℚ) = 0 := by
  rw [← Nat.cast_ofNat (R := PowerSeries ℚ)]
  exact Derivation.map_natCast _ _

noncomputable def G : PowerSeries ℚ := PowerSeries.mk a

/-- The series whose coefficients define the sequence. -/
noncomputable def F : PowerSeries ℚ := ((0) + (1) * S) * (1 - 2 * X - X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6 : PowerSeries ℚ)⁻¹

lemma hD0 : constantCoeff (1 - 2 * X - X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6 : PowerSeries ℚ) ≠ 0 := by
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero,
    constantCoeff_X, hS0]
  norm_num

lemma hF : (1 - 2 * X - X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6) * F = (0) + (1) * S := by
  unfold F
  rw [mul_comm, mul_assoc, PowerSeries.inv_mul_cancel _ hD0, mul_one]

lemma a_eq (j : ℕ) : a j = coeff j F := by
  unfold a F
  congr 1
  try ring


lemma hGF : G = F := by
  ext j
  rw [G, coeff_mk, a_eq]

lemma hG : (1 - 2 * X - X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6) * G = (0) + (1) * S := by
  rw [hGF]
  exact hF

lemma dP : derivative ℚ (0 : PowerSeries ℚ) = 0 := by
  simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma dQ : derivative ℚ (1 : PowerSeries ℚ) = 0 := by
  simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma dDl : derivative ℚ (1 - 2 * X - X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6 : PowerSeries ℚ) = -2 - 2 * X - 4 * X ^ 3 - 10 * X ^ 4 + 6 * X ^ 5 := by
  simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma dD : derivative ℚ ((1 - 2 * X - X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6) : PowerSeries ℚ) = -2 - 2 * X - 4 * X ^ 3 - 10 * X ^ 4 + 6 * X ^ 5 := by
  simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring


lemma hE0 : (2 - 8 * X + 4 * X ^ 2 + 8 * X ^ 3 - 2 * X ^ 4 + 24 * X ^ 6 - 2 * X ^ 8 + 8 * X ^ 9 + 4 * X ^ 10 - 8 * X ^ 11 + 2 * X ^ 12) * derivative ℚ G + (-2 + 2 * X + 6 * X ^ 2 - 2 * X ^ 3 + 36 * X ^ 5 - 4 * X ^ 7 + 18 * X ^ 8 + 10 * X ^ 9 - 22 * X ^ 10 + 6 * X ^ 11) * G = 0 := by
  have h := ode S R ((1 - 2 * X - X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6)) (0) (1) G hS hG
  rw [dP, dQ, dD] at h
  unfold R at h
  rw [dDl] at h
  linear_combination h


lemma hu : (2 - 8 * X + 4 * X ^ 2 + 8 * X ^ 3 - 2 * X ^ 4 + 24 * X ^ 6 - 2 * X ^ 8 + 8 * X ^ 9 + 4 * X ^ 10 - 8 * X ^ 11 + 2 * X ^ 12 : PowerSeries ℚ) ≠ 0 := by
  intro h
  have h' := congrArg constantCoeff h
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero,
    constantCoeff_X] at h'
  norm_num at h'

lemma hT : (X + X ^ 2 - 7 * X ^ 3 - 3 * X ^ 4 - X ^ 5 - 5 * X ^ 6 - 5 * X ^ 7 + 3 * X ^ 8) * derivative ℚ G + (-X - 4 * X ^ 2 - 3 * X ^ 3 - 2 * X ^ 4 - 11 * X ^ 5 - 12 * X ^ 6 + 9 * X ^ 7) * G - (0) = 0 := by
  have hc : (X ^ 0 * (2 - 8 * X + 4 * X ^ 2 + 8 * X ^ 3 - 2 * X ^ 4 + 24 * X ^ 6 - 2 * X ^ 8 + 8 * X ^ 9 + 4 * X ^ 10 - 8 * X ^ 11 + 2 * X ^ 12) : PowerSeries ℚ) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hu
  have hm : (X ^ 0 * (2 - 8 * X + 4 * X ^ 2 + 8 * X ^ 3 - 2 * X ^ 4 + 24 * X ^ 6 - 2 * X ^ 8 + 8 * X ^ 9 + 4 * X ^ 10 - 8 * X ^ 11 + 2 * X ^ 12)) ^ 1 * ((X + X ^ 2 - 7 * X ^ 3 - 3 * X ^ 4 - X ^ 5 - 5 * X ^ 6 - 5 * X ^ 7 + 3 * X ^ 8) * derivative ℚ G + (-X - 4 * X ^ 2 - 3 * X ^ 3 - 2 * X ^ 4 - 11 * X ^ 5 - 12 * X ^ 6 + 9 * X ^ 7) * G - (0)) = 0 := by
    linear_combination (X + X ^ 2 - 7 * X ^ 3 - 3 * X ^ 4 - X ^ 5 - 5 * X ^ 6 - 5 * X ^ 7 + 3 * X ^ 8) * hE0
  exact (mul_eq_zero.mp hm).resolve_left (pow_ne_zero _ hc)

/-- Iterated derivative. -/
noncomputable def dn : ℕ → PowerSeries ℚ → PowerSeries ℚ
  | 0, f => f
  | (j + 1), f => dn j (derivative ℚ f)

lemma coeff_dn (j : ℕ) : ∀ (m : ℕ) (f : PowerSeries ℚ),
    coeff m (dn j f) = coeff (m + j) f * ((m + j).descFactorial j : ℚ) := by
  induction j with
  | zero =>
    intro m f
    simp [dn]
  | succ j ih =>
    intro m f
    rw [dn, ih, coeff_derivative, show m + (j + 1) = m + j + 1 from rfl, Nat.succ_descFactorial_succ]
    push_cast
    ring

lemma coeff_term (b : ℕ → ℚ) (i j e t : ℕ) (he : e = i + j) (hi : i ≤ t) :
    coeff t (X ^ e * dn j (PowerSeries.mk b)) = b (t - i) * ((t - i).descFactorial j : ℚ) := by
  subst he
  rw [coeff_X_pow_mul']
  by_cases h : i + j ≤ t
  · rw [if_pos h, coeff_dn, coeff_mk]
    have e1 : t - (i + j) + j = t - i := by omega
    rw [e1]
  · rw [if_neg h]
    have hz : (t - i).descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [hz]
    simp

lemma df1 (t : ℕ) : (t.descFactorial 1 : ℚ) = t := by
  simp

lemma df2 (t : ℕ) : (t.descFactorial 2 : ℚ) = t * ((t : ℚ) - 1) := by
  rcases t with _ | t
  · simp
  · rw [Nat.succ_descFactorial_succ, Nat.descFactorial_one]
    push_cast
    ring

lemma df3 (t : ℕ) : (t.descFactorial 3 : ℚ) = t * ((t : ℚ) - 1) * ((t : ℚ) - 2) := by
  rcases t with _ | _ | t
  · simp
  · simp [Nat.descFactorial]
  · rw [Nat.succ_descFactorial_succ, Nat.succ_descFactorial_succ, Nat.descFactorial_one]
    push_cast
    ring

lemma dn0 : dn 0 (PowerSeries.mk a) = G := rfl

lemma dn1 : dn 1 (PowerSeries.mk a) = derivative ℚ G := rfl

lemma dn2 : dn 2 (PowerSeries.mk a) = derivative ℚ (derivative ℚ G) := rfl

lemma dn3 : dn 3 (PowerSeries.mk a) = derivative ℚ (derivative ℚ (derivative ℚ G)) := rfl


lemma hTC : C (1 : ℚ) * (X ^ 1 * dn 1 (PowerSeries.mk a))
      + C (1 : ℚ) * (X ^ 2 * dn 1 (PowerSeries.mk a))
      + C (-7 : ℚ) * (X ^ 3 * dn 1 (PowerSeries.mk a))
      + C (-3 : ℚ) * (X ^ 4 * dn 1 (PowerSeries.mk a))
      + C (-1 : ℚ) * (X ^ 5 * dn 1 (PowerSeries.mk a))
      + C (-5 : ℚ) * (X ^ 6 * dn 1 (PowerSeries.mk a))
      + C (-5 : ℚ) * (X ^ 7 * dn 1 (PowerSeries.mk a))
      + C (3 : ℚ) * (X ^ 8 * dn 1 (PowerSeries.mk a))
      + C (-1 : ℚ) * (X ^ 1 * dn 0 (PowerSeries.mk a))
      + C (-4 : ℚ) * (X ^ 2 * dn 0 (PowerSeries.mk a))
      + C (-3 : ℚ) * (X ^ 3 * dn 0 (PowerSeries.mk a))
      + C (-2 : ℚ) * (X ^ 4 * dn 0 (PowerSeries.mk a))
      + C (-11 : ℚ) * (X ^ 5 * dn 0 (PowerSeries.mk a))
      + C (-12 : ℚ) * (X ^ 6 * dn 0 (PowerSeries.mk a))
      + C (9 : ℚ) * (X ^ 7 * dn 0 (PowerSeries.mk a)) = 0 := by
  have h := hT
  simp only [dn0, dn1, dn2, dn3]
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h


lemma hrec (N : ℕ) :
    (((N : ℚ) + 7)) * a (N + 7) + (((N : ℚ) + 7) - 2) * a (N + 6)
      + (-7 * ((N : ℚ) + 7) + 10) * a (N + 5) + (-3 * ((N : ℚ) + 7) + 6) * a (N + 4)
      + (-((N : ℚ) + 7) + 2) * a (N + 3) + (-5 * ((N : ℚ) + 7) + 14) * a (N + 2)
      + (-5 * ((N : ℚ) + 7) + 18) * a (N + 1) + (3 * ((N : ℚ) + 7) - 12) * a N = 0 := by
  have h := congrArg (coeff (N + 7)) hTC
  have e0_1 := coeff_term a 0 1 1 (N + 7) rfl (by omega)
  have e1_1 := coeff_term a 1 1 2 (N + 7) rfl (by omega)
  have e2_1 := coeff_term a 2 1 3 (N + 7) rfl (by omega)
  have e3_1 := coeff_term a 3 1 4 (N + 7) rfl (by omega)
  have e4_1 := coeff_term a 4 1 5 (N + 7) rfl (by omega)
  have e5_1 := coeff_term a 5 1 6 (N + 7) rfl (by omega)
  have e6_1 := coeff_term a 6 1 7 (N + 7) rfl (by omega)
  have e7_1 := coeff_term a 7 1 8 (N + 7) rfl (by omega)
  have e1_0 := coeff_term a 1 0 1 (N + 7) rfl (by omega)
  have e2_0 := coeff_term a 2 0 2 (N + 7) rfl (by omega)
  have e3_0 := coeff_term a 3 0 3 (N + 7) rfl (by omega)
  have e4_0 := coeff_term a 4 0 4 (N + 7) rfl (by omega)
  have e5_0 := coeff_term a 5 0 5 (N + 7) rfl (by omega)
  have e6_0 := coeff_term a 6 0 6 (N + 7) rfl (by omega)
  have e7_0 := coeff_term a 7 0 7 (N + 7) rfl (by omega)
  have t1 : N + 7 - 1 = N + 6 := by omega
  have t2 : N + 7 - 2 = N + 5 := by omega
  have t3 : N + 7 - 3 = N + 4 := by omega
  have t4 : N + 7 - 4 = N + 3 := by omega
  have t5 : N + 7 - 5 = N + 2 := by omega
  have t6 : N + 7 - 6 = N + 1 := by omega
  have t7 : N + 7 - 7 = N := by omega
  simp only [LinearMap.map_add, LinearMap.map_sub, coeff_C_mul, e0_1, e1_1, e2_1, e3_1, e4_1, e5_1, e6_1, e7_1, e1_0, e2_0, e3_0, e4_0, e5_0, e6_0, e7_0, LinearMap.map_zero,
    mul_zero, sub_zero, add_zero] at h
  simp only [t1, t2, t3, t4, t5, t6, t7, Nat.sub_zero, df1, df2, df3, Nat.descFactorial_zero, Nat.cast_one,
    mul_one] at h
  push_cast at h
  linear_combination h

end OMA.P182904

theorem OMA.solution : type_of% @OMA.S_oeis_a182904.main := by
  intro n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 7 := ⟨n - 7, by omega⟩
  have h := OMA.P182904.hrec N
  have t1 : N + 7 - 1 = N + 6 := by omega
  have t2 : N + 7 - 2 = N + 5 := by omega
  have t3 : N + 7 - 3 = N + 4 := by omega
  have t4 : N + 7 - 4 = N + 3 := by omega
  have t5 : N + 7 - 5 = N + 2 := by omega
  have t6 : N + 7 - 6 = N + 1 := by omega
  have t7 : N + 7 - 7 = N := by omega
  simp only [t1, t2, t3, t4, t5, t6, t7]
  push_cast
  linear_combination h
