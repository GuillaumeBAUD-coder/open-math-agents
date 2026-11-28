import OMAStatements.S_oeis_a126180

-- Problem: OEIS A126180. The sequence is given by the generating function
-- A(x) = (P + Q * sqrt(R)) / D with polynomials P, Q, D, R; the conjectured recurrence is the
-- coefficientwise form of a second order linear differential equation for A.
-- Proof. S = sqrt(R) satisfies S^2 = R, hence 2 R S' = R' S. Differentiating A D = P + Q S and
-- eliminating S and S' gives c1 A' + c0 A = c with c1 = 2RDQ, c0 = 2RQD' - (2RQ' + QR')D,
-- c = 2RQP' - (2RQ' + QR')P. Differentiating once more expresses A'' through A' and A, and the
-- operator of the recurrence, b2 (x d/dx)^2 + b1 (x d/dx) + b0, then sends A to a polynomial T.
-- Comparing the coefficients of x^N for N large gives the recurrence.

open OMA.S_oeis_a126180 PowerSeries

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


lemma OMA.cXtt (c : ℚ) (j N m : ℕ) (f : ℚ⟦X⟧) (h : N = m + j) :
    coeff N (C c * (X ^ j * (X * d⁄dX ℚ (X * d⁄dX ℚ f))))
      = c * ((m : ℚ) * ((m : ℚ) * coeff m f)) := by
  subst h
  rw [coeff_C_mul, coeff_X_pow_mul, OMA.coeff_theta, OMA.coeff_theta]

/-- The generating function of the sequence. -/
noncomputable def OMA.A : ℚ⟦X⟧ :=
    ((-2 + 21 * X - 73 * X ^ 2 + 99 * X ^ 3 - 45 * X ^ 4 + (2 - 15 * X + 32 * X ^ 2 - 15 * X ^ 3) * S)
      * (2 - 12 * X + 10 * X ^ 2 : PowerSeries ℚ)⁻¹)

lemma OMA.a_eq (m : ℕ) : a m = coeff (m + 2) OMA.A := rfl

lemma OMA.dS : 2 * (1 - 6 * X + 5 * X ^ 2 : ℚ⟦X⟧) * d⁄dX ℚ S = (-6 + 10 * X : ℚ⟦X⟧) * S := by
  have E := congrArg (d⁄dX ℚ) OMA.S_sq
  have hR : R = (1 - 6 * X + 5 * X ^ 2 : ℚ⟦X⟧) := rfl
  have h2 := OMA.S_sq
  rw [hR] at E h2
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination S * E - (2 * d⁄dX ℚ S) * h2

lemma OMA.AD : OMA.A * (2 - 12 * X + 10 * X ^ 2 : PowerSeries ℚ) = (-2 + 21 * X - 73 * X ^ 2 + 99 * X ^ 3 - 45 * X ^ 4 + (2 - 15 * X + 32 * X ^ 2 - 15 * X ^ 3) * S) := by
  unfold OMA.A
  have hD : constantCoeff (2 - 12 * X + 10 * X ^ 2 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
    norm_num
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hD, mul_one]

lemma OMA.dAD : (2 - 12 * X + 10 * X ^ 2 : ℚ⟦X⟧) * d⁄dX ℚ OMA.A + OMA.A * (-12 + 20 * X : ℚ⟦X⟧)
    = (21 - 146 * X + 297 * X ^ 2 - 180 * X ^ 3 : ℚ⟦X⟧) + (-15 + 64 * X - 45 * X ^ 2 : ℚ⟦X⟧) * S + (2 - 15 * X + 32 * X ^ 2 - 15 * X ^ 3 : ℚ⟦X⟧) * d⁄dX ℚ S := by
  have E := congrArg (d⁄dX ℚ) OMA.AD
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination E

lemma OMA.fo : (8 - 156 * X + 1216 * X ^ 2 - 4836 * X ^ 3 + 10408 * X ^ 4 - 11940 * X ^ 5 + 6800 * X ^ 6 - 1500 * X ^ 7 : ℚ⟦X⟧) * d⁄dX ℚ OMA.A + (36 - 612 * X + 3888 * X ^ 2 - 11512 * X ^ 3 + 16500 * X ^ 4 - 11300 * X ^ 5 + 3000 * X ^ 6 : ℚ⟦X⟧) * OMA.A = (72 * X ^ 2 - 944 * X ^ 3 + 4560 * X ^ 4 - 10048 * X ^ 5 + 9960 * X ^ 6 - 3600 * X ^ 7 : ℚ⟦X⟧) := by
  have F3 := OMA.AD
  have F4 := OMA.dAD
  have hS := OMA.dS
  linear_combination (2 * (1 - 6 * X + 5 * X ^ 2 : ℚ⟦X⟧) * (2 - 15 * X + 32 * X ^ 2 - 15 * X ^ 3 : ℚ⟦X⟧)) * F4
    - (2 * (1 - 6 * X + 5 * X ^ 2 : ℚ⟦X⟧) * (-15 + 64 * X - 45 * X ^ 2 : ℚ⟦X⟧) + (2 - 15 * X + 32 * X ^ 2 - 15 * X ^ 3 : ℚ⟦X⟧) * (-6 + 10 * X : ℚ⟦X⟧)) * F3 + ((2 - 15 * X + 32 * X ^ 2 - 15 * X ^ 3 : ℚ⟦X⟧) * (2 - 15 * X + 32 * X ^ 2 - 15 * X ^ 3 : ℚ⟦X⟧)) * hS

lemma OMA.fo2 : (8 - 156 * X + 1216 * X ^ 2 - 4836 * X ^ 3 + 10408 * X ^ 4 - 11940 * X ^ 5 + 6800 * X ^ 6 - 1500 * X ^ 7 : ℚ⟦X⟧) * d⁄dX ℚ (d⁄dX ℚ OMA.A) + ((-156 + 2432 * X - 14508 * X ^ 2 + 41632 * X ^ 3 - 59700 * X ^ 4 + 40800 * X ^ 5 - 10500 * X ^ 6 : ℚ⟦X⟧) + (36 - 612 * X + 3888 * X ^ 2 - 11512 * X ^ 3 + 16500 * X ^ 4 - 11300 * X ^ 5 + 3000 * X ^ 6 : ℚ⟦X⟧)) * d⁄dX ℚ OMA.A
    + (-612 + 7776 * X - 34536 * X ^ 2 + 66000 * X ^ 3 - 56500 * X ^ 4 + 18000 * X ^ 5 : ℚ⟦X⟧) * OMA.A = (144 * X - 2832 * X ^ 2 + 18240 * X ^ 3 - 50240 * X ^ 4 + 59760 * X ^ 5 - 25200 * X ^ 6 : ℚ⟦X⟧) := by
  have E := congrArg (d⁄dX ℚ) OMA.fo
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination E

lemma OMA.th2 : X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A) = X * X * d⁄dX ℚ (d⁄dX ℚ OMA.A) + X * d⁄dX ℚ OMA.A := by
  rw [Derivation.leibniz]
  simp only [derivative_X, smul_eq_mul]
  ring

lemma OMA.ode : (1 : ℚ⟦X⟧) * ((-478 + 4620 * X - 12902 * X ^ 2 + 8760 * X ^ 3 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))
    + (3460 - 30177 * X + 76676 * X ^ 2 - 42315 * X ^ 3 : ℚ⟦X⟧) * (X * d⁄dX ℚ OMA.A)
    + (13419 * X - 77157 * X ^ 2 + 49590 * X ^ 3 : ℚ⟦X⟧) * OMA.A) - (18234 * X ^ 3 - 38484 * X ^ 4 : ℚ⟦X⟧) = 0 := by
  have h1' := OMA.fo
  have h2' := OMA.fo2
  have h3' := OMA.th2
  have key : ((8 - 156 * X + 1216 * X ^ 2 - 4836 * X ^ 3 + 10408 * X ^ 4 - 11940 * X ^ 5 + 6800 * X ^ 6 - 1500 * X ^ 7 : ℚ⟦X⟧) * (8 - 156 * X + 1216 * X ^ 2 - 4836 * X ^ 3 + 10408 * X ^ 4 - 11940 * X ^ 5 + 6800 * X ^ 6 - 1500 * X ^ 7 : ℚ⟦X⟧))
      * ((1 : ℚ⟦X⟧) * ((-478 + 4620 * X - 12902 * X ^ 2 + 8760 * X ^ 3 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))
    + (3460 - 30177 * X + 76676 * X ^ 2 - 42315 * X ^ 3 : ℚ⟦X⟧) * (X * d⁄dX ℚ OMA.A)
    + (13419 * X - 77157 * X ^ 2 + 49590 * X ^ 3 : ℚ⟦X⟧) * OMA.A) - (18234 * X ^ 3 - 38484 * X ^ 4 : ℚ⟦X⟧)) = 0 := by
    linear_combination
      ((1 : ℚ⟦X⟧) * (-478 + 4620 * X - 12902 * X ^ 2 + 8760 * X ^ 3 : ℚ⟦X⟧) * (8 - 156 * X + 1216 * X ^ 2 - 4836 * X ^ 3 + 10408 * X ^ 4 - 11940 * X ^ 5 + 6800 * X ^ 6 - 1500 * X ^ 7 : ℚ⟦X⟧) * (8 - 156 * X + 1216 * X ^ 2 - 4836 * X ^ 3 + 10408 * X ^ 4 - 11940 * X ^ 5 + 6800 * X ^ 6 - 1500 * X ^ 7 : ℚ⟦X⟧)) * h3'
        + ((1 : ℚ⟦X⟧) * (-478 + 4620 * X - 12902 * X ^ 2 + 8760 * X ^ 3 : ℚ⟦X⟧) * X ^ 2 * (8 - 156 * X + 1216 * X ^ 2 - 4836 * X ^ 3 + 10408 * X ^ 4 - 11940 * X ^ 5 + 6800 * X ^ 6 - 1500 * X ^ 7 : ℚ⟦X⟧)) * h2'
        + ((1 : ℚ⟦X⟧) * (23856 * X - 727008 * X ^ 2 + 9547556 * X ^ 3 - 70748448 * X ^ 4 + 325408672 * X ^ 5 - 963582720 * X ^ 6 + 1846784392 * X ^ 7 - 2250055200 * X ^ 8 + 1666336400 * X ^ 9 - 679020000 * X ^ 10 + 116032500 * X ^ 11 : ℚ⟦X⟧)) * h1'
  have hc1 : (8 - 156 * X + 1216 * X ^ 2 - 4836 * X ^ 3 + 10408 * X ^ 4 - 11940 * X ^ 5 + 6800 * X ^ 6 - 1500 * X ^ 7 : ℚ⟦X⟧) ≠ 0 := by
    have e : (8 - 156 * X + 1216 * X ^ 2 - 4836 * X ^ 3 + 10408 * X ^ 4 - 11940 * X ^ 5 + 6800 * X ^ 6 - 1500 * X ^ 7 : ℚ⟦X⟧) = 2 * (1 - 6 * X + 5 * X ^ 2 : ℚ⟦X⟧) * (2 - 12 * X + 10 * X ^ 2 : ℚ⟦X⟧) * (X ^ 0 * (2 - 15 * X + 32 * X ^ 2 - 15 * X ^ 3 : ℚ⟦X⟧)) := by ring
    rw [e]
    have h1 : (2 * (1 - 6 * X + 5 * X ^ 2 : ℚ⟦X⟧) : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    have h2 : (2 - 12 * X + 10 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    have h3 : (2 - 15 * X + 32 * X ^ 2 - 15 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    exact mul_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero (pow_ne_zero _ X_ne_zero) h3)
  exact (mul_eq_zero.mp key).resolve_left (mul_ne_zero hc1 hc1)

theorem OMA.solution : type_of% @OMA.S_oeis_a126180.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hexp : C (-478 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (4620 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (-12902 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (8760 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (3460 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ OMA.A))
      + C (-30177 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ OMA.A))
      + C (76676 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ OMA.A))
      + C (-42315 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ OMA.A))
      + C (13419 : ℚ) * (X ^ 1 * OMA.A)
      + C (-77157 : ℚ) * (X ^ 2 * OMA.A)
      + C (49590 : ℚ) * (X ^ 3 * OMA.A)
      = C (18234 : ℚ) * X ^ 3 + C (-38484 : ℚ) * X ^ 4 := by
    have h := OMA.ode
    simp only [map_neg, map_ofNat, map_one]
    linear_combination h
  have hc := congrArg (coeff (k + 6)) hexp
  have s0 : coeff (k + 6) (C (-478 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-478 : ℚ) * (((k + 6 : ℕ) : ℚ) * (((k + 6 : ℕ) : ℚ) * coeff (k + 6) OMA.A)) :=
    OMA.cXtt _ 0 _ (k + 6) _ (by omega)
  have s1 : coeff (k + 6) (C (4620 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (4620 : ℚ) * (((k + 5 : ℕ) : ℚ) * (((k + 5 : ℕ) : ℚ) * coeff (k + 5) OMA.A)) :=
    OMA.cXtt _ 1 _ (k + 5) _ (by omega)
  have s2 : coeff (k + 6) (C (-12902 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-12902 : ℚ) * (((k + 4 : ℕ) : ℚ) * (((k + 4 : ℕ) : ℚ) * coeff (k + 4) OMA.A)) :=
    OMA.cXtt _ 2 _ (k + 4) _ (by omega)
  have s3 : coeff (k + 6) (C (8760 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (8760 : ℚ) * (((k + 3 : ℕ) : ℚ) * (((k + 3 : ℕ) : ℚ) * coeff (k + 3) OMA.A)) :=
    OMA.cXtt _ 3 _ (k + 3) _ (by omega)
  have t0 : coeff (k + 6) (C (3460 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ OMA.A)))
      = (3460 : ℚ) * (((k + 6 : ℕ) : ℚ) * coeff (k + 6) OMA.A) :=
    OMA.cXt _ 0 _ (k + 6) _ (by omega)
  have t1 : coeff (k + 6) (C (-30177 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ OMA.A)))
      = (-30177 : ℚ) * (((k + 5 : ℕ) : ℚ) * coeff (k + 5) OMA.A) :=
    OMA.cXt _ 1 _ (k + 5) _ (by omega)
  have t2 : coeff (k + 6) (C (76676 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ OMA.A)))
      = (76676 : ℚ) * (((k + 4 : ℕ) : ℚ) * coeff (k + 4) OMA.A) :=
    OMA.cXt _ 2 _ (k + 4) _ (by omega)
  have t3 : coeff (k + 6) (C (-42315 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ OMA.A)))
      = (-42315 : ℚ) * (((k + 3 : ℕ) : ℚ) * coeff (k + 3) OMA.A) :=
    OMA.cXt _ 3 _ (k + 3) _ (by omega)
  have f1 : coeff (k + 6) (C (13419 : ℚ) * (X ^ 1 * OMA.A))
      = (13419 : ℚ) * coeff (k + 5) OMA.A := OMA.cXf _ 1 _ (k + 5) _ (by omega)
  have f2 : coeff (k + 6) (C (-77157 : ℚ) * (X ^ 2 * OMA.A))
      = (-77157 : ℚ) * coeff (k + 4) OMA.A := OMA.cXf _ 2 _ (k + 4) _ (by omega)
  have f3 : coeff (k + 6) (C (49590 : ℚ) * (X ^ 3 * OMA.A))
      = (49590 : ℚ) * coeff (k + 3) OMA.A := OMA.cXf _ 3 _ (k + 3) _ (by omega)
  have z3 : coeff (k + 6) (C (18234 : ℚ) * X ^ 3 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 3 _ (by omega)
  have z4 : coeff (k + 6) (C (-38484 : ℚ) * X ^ 4 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 4 _ (by omega)
  simp only [map_add, map_zero, s0, s1, s2, s3, t0, t1, t2, t3, f1, f2, f3, z3, z4] at hc
  have e0 : a (k + 4) = coeff (k + 6) OMA.A := by
    have h : k + 4 + 2 = k + 6 := by omega
    rw [OMA.a_eq, h]
  have e1 : a (k + 4 - 1) = coeff (k + 5) OMA.A := by
    have h : k + 4 - 1 + 2 = k + 5 := by omega
    rw [OMA.a_eq, h]
  have e2 : a (k + 4 - 2) = coeff (k + 4) OMA.A := by
    have h : k + 4 - 2 + 2 = k + 4 := by omega
    rw [OMA.a_eq, h]
  have e3 : a (k + 4 - 3) = coeff (k + 3) OMA.A := by
    have h : k + 4 - 3 + 2 = k + 3 := by omega
    rw [OMA.a_eq, h]
  rw [e0, e1, e2, e3]
  push_cast at hc ⊢
  linear_combination (1 / 1 : ℚ) * hc
