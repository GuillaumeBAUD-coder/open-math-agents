import OMAStatements.S_oeis_a194724

-- Problem: OEIS A194724. The sequence is given by the generating function
-- A(x) = (P + Q * sqrt(R)) / D with polynomials P, Q, D, R; the conjectured recurrence is the
-- coefficientwise form of a first order linear differential equation for A.
-- Proof. S = sqrt(R) satisfies S^2 = R, hence 2 R S' = R' S. Differentiating A D = P + Q S and
-- eliminating S and S' gives 2RDQ A' + (2RQD' - (2RQ' + QR')D) A = 2RQP' - (2RQ' + QR')P.
-- The recurrence corresponds to a1 A' + a0 A = T, which is this equation up to a common factor;
-- comparing the coefficients of x^N for N large gives the recurrence.

open OMA.S_oeis_a194724 PowerSeries

lemma OMA.d_ofNat (n : ℕ) [n.AtLeastTwo] : d⁄dX ℚ (ofNat(n) : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ _

lemma OMA.hasSubst : HasSubst (R - 1) := by
  apply HasSubst.of_constantCoeff_zero'
  unfold R
  simp

lemma OMA.S_sq : S * S = R := by
  unfold S
  have h := OMA.hasSubst
  have e : (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) := by norm_num
  rw [← subst_mul h, ← binomialSeries_add, e, binomialSeries_nat, pow_one, subst_add h, subst_X h,
    ← coe_substAlgHom h, map_one]
  ring

lemma OMA.coeff_theta (f : ℚ⟦X⟧) (m : ℕ) : coeff m (X * d⁄dX ℚ f) = (m : ℚ) * coeff m f := by
  rcases m with _ | m
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

lemma OMA.cXt (c : ℚ) (j N m : ℕ) (f : ℚ⟦X⟧) (h : N = m + j) :
    coeff N (C c * (X ^ j * (X * d⁄dX ℚ f))) = c * ((m : ℚ) * coeff m f) := by
  subst h
  rw [coeff_C_mul, coeff_X_pow_mul, OMA.coeff_theta]

lemma OMA.cXf (c : ℚ) (j N m : ℕ) (f : ℚ⟦X⟧) (h : N = m + j) :
    coeff N (C c * (X ^ j * f)) = c * coeff m f := by
  subst h
  rw [coeff_C_mul, coeff_X_pow_mul]

lemma OMA.cX0 (c : ℚ) (j N : ℕ) (h : j < N) : coeff N (C c * X ^ j : ℚ⟦X⟧) = 0 := by
  rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

lemma OMA.ne_of_cc (f : ℚ⟦X⟧) (h : constantCoeff f ≠ 0) : f ≠ 0 := by
  intro h0
  rw [h0] at h
  simp at h


/-- The generating function of the sequence. -/
noncomputable def OMA.A : ℚ⟦X⟧ :=
    ((1 - 24 * X + S)
      * (2 - 32 * X : PowerSeries ℚ)⁻¹)

lemma OMA.a_eq (m : ℕ) : a m = coeff m OMA.A := rfl

lemma OMA.dS : 2 * (1 - 12 * X : ℚ⟦X⟧) * d⁄dX ℚ S = (-12 : ℚ⟦X⟧) * S := by
  have E := congrArg (d⁄dX ℚ) OMA.S_sq
  have hR : R = (1 - 12 * X : ℚ⟦X⟧) := rfl
  have h2 := OMA.S_sq
  rw [hR] at E h2
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination S * E - (2 * d⁄dX ℚ S) * h2

lemma OMA.AD : OMA.A * (2 - 32 * X : PowerSeries ℚ) = (1 - 24 * X + S) := by
  unfold OMA.A
  have hD : constantCoeff (2 - 32 * X : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
    norm_num
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hD, mul_one]

lemma OMA.dAD : (2 - 32 * X : ℚ⟦X⟧) * d⁄dX ℚ OMA.A + OMA.A * (-32 : ℚ⟦X⟧)
    = (-24 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * S + (1 : ℚ⟦X⟧) * d⁄dX ℚ S := by
  have E := congrArg (d⁄dX ℚ) OMA.AD
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination E

lemma OMA.ode : (1 : ℚ⟦X⟧) * ((1 - 28 * X + 192 * X ^ 2 : ℚ⟦X⟧) * (X * d⁄dX ℚ OMA.A)
    + (-10 * X + 96 * X ^ 2 : ℚ⟦X⟧) * OMA.A) - (-9 * X + 72 * X ^ 2 : ℚ⟦X⟧) = 0 := by
  have F3 := OMA.AD
  have F4 := OMA.dAD
  have hS := OMA.dS
  have key : (2 * (1 - 12 * X : ℚ⟦X⟧) * (2 - 32 * X : ℚ⟦X⟧) * (1 : ℚ⟦X⟧))
      * ((1 : ℚ⟦X⟧) * ((1 - 28 * X + 192 * X ^ 2 : ℚ⟦X⟧) * (X * d⁄dX ℚ OMA.A)
    + (-10 * X + 96 * X ^ 2 : ℚ⟦X⟧) * OMA.A) - (-9 * X + 72 * X ^ 2 : ℚ⟦X⟧)) = 0 := by
    linear_combination
      ((1 : ℚ⟦X⟧) * (X * (1 - 28 * X + 192 * X ^ 2 : ℚ⟦X⟧)) * 2 * (1 - 12 * X : ℚ⟦X⟧) * (1 : ℚ⟦X⟧)) * F4
        - ((1 : ℚ⟦X⟧) * (X * (1 - 28 * X + 192 * X ^ 2 : ℚ⟦X⟧)) * (2 * (1 - 12 * X : ℚ⟦X⟧) * (0 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (-12 : ℚ⟦X⟧))) * F3
        + ((1 : ℚ⟦X⟧) * (X * (1 - 28 * X + 192 * X ^ 2 : ℚ⟦X⟧)) * (1 : ℚ⟦X⟧) * (1 : ℚ⟦X⟧)) * hS
  have h1 : (2 * (1 - 12 * X : ℚ⟦X⟧) : ℚ⟦X⟧) ≠ 0 := by
    refine OMA.ne_of_cc _ ?_
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
    norm_num
  have h2 : (2 - 32 * X : ℚ⟦X⟧) ≠ 0 := by
    refine OMA.ne_of_cc _ ?_
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
    norm_num
  have h3 : (1 : ℚ⟦X⟧) ≠ 0 := by
    have e : (1 : ℚ⟦X⟧) = X ^ 0 * (1 : ℚ⟦X⟧) := by ring
    rw [e]
    refine mul_ne_zero (pow_ne_zero _ X_ne_zero) (OMA.ne_of_cc _ ?_)
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
    norm_num
  exact (mul_eq_zero.mp key).resolve_left (mul_ne_zero (mul_ne_zero h1 h2) h3)

theorem OMA.solution : type_of% @OMA.S_oeis_a194724.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hexp : C (1 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ OMA.A))
      + C (-28 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ OMA.A))
      + C (192 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ OMA.A))
      + C (-10 : ℚ) * (X ^ 1 * OMA.A)
      + C (96 : ℚ) * (X ^ 2 * OMA.A)
      = C (-9 : ℚ) * X ^ 1 + C (72 : ℚ) * X ^ 2 := by
    have h := OMA.ode
    simp only [map_neg, map_ofNat, map_one]
    linear_combination h
  have hc := congrArg (coeff (k + 3)) hexp
  have t0 : coeff (k + 3) (C (1 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ OMA.A)))
      = (1 : ℚ) * (((k + 3 : ℕ) : ℚ) * coeff (k + 3) OMA.A) :=
    OMA.cXt _ 0 _ (k + 3) _ (by omega)
  have t1 : coeff (k + 3) (C (-28 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ OMA.A)))
      = (-28 : ℚ) * (((k + 2 : ℕ) : ℚ) * coeff (k + 2) OMA.A) :=
    OMA.cXt _ 1 _ (k + 2) _ (by omega)
  have t2 : coeff (k + 3) (C (192 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ OMA.A)))
      = (192 : ℚ) * (((k + 1 : ℕ) : ℚ) * coeff (k + 1) OMA.A) :=
    OMA.cXt _ 2 _ (k + 1) _ (by omega)
  have f1 : coeff (k + 3) (C (-10 : ℚ) * (X ^ 1 * OMA.A))
      = (-10 : ℚ) * coeff (k + 2) OMA.A := OMA.cXf _ 1 _ (k + 2) _ (by omega)
  have f2 : coeff (k + 3) (C (96 : ℚ) * (X ^ 2 * OMA.A))
      = (96 : ℚ) * coeff (k + 1) OMA.A := OMA.cXf _ 2 _ (k + 1) _ (by omega)
  have z1 : coeff (k + 3) (C (-9 : ℚ) * X ^ 1 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 1 _ (by omega)
  have z2 : coeff (k + 3) (C (72 : ℚ) * X ^ 2 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 2 _ (by omega)
  simp only [map_add, map_zero, t0, t1, t2, f1, f2, z1, z2] at hc
  have e0 : a (k + 3) = coeff (k + 3) OMA.A := by
    have h : k + 3 = k + 3 := by omega
    rw [OMA.a_eq, h]
  have e1 : a (k + 3 - 1) = coeff (k + 2) OMA.A := by
    have h : k + 3 - 1 = k + 2 := by omega
    rw [OMA.a_eq, h]
  have e2 : a (k + 3 - 2) = coeff (k + 1) OMA.A := by
    have h : k + 3 - 2 = k + 1 := by omega
    rw [OMA.a_eq, h]
  rw [e0, e1, e2]
  push_cast at hc ⊢
  linear_combination (1 / 1 : ℚ) * hc
