import OMAStatements.S_oeis_a217711

-- Problem: OEIS A217711. The sequence is given by the generating function
-- A(x) = (P + Q * sqrt(R)) / D with polynomials P, Q, D, R; the conjectured recurrence is the
-- coefficientwise form of a second order linear differential equation for A.
-- Proof. S = sqrt(R) satisfies S^2 = R, hence 2 R S' = R' S. Differentiating A D = P + Q S and
-- eliminating S and S' gives c1 A' + c0 A = c with c1 = 2RDQ, c0 = 2RQD' - (2RQ' + QR')D,
-- c = 2RQP' - (2RQ' + QR')P. Differentiating once more expresses A'' through A' and A, and the
-- operator of the recurrence, b2 (x d/dx)^2 + b1 (x d/dx) + b0, then sends A to a polynomial T.
-- Comparing the coefficients of x^N for N large gives the recurrence.

open OMA.S_oeis_a217711 PowerSeries

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
    ((-1 + 12 * X - 52 * X ^ 2 + 88 * X ^ 3 - 32 * X ^ 4 + (1 - 10 * X + 34 * X ^ 2 - 36 * X ^ 3) * S)
      * (2 - 24 * X + 96 * X ^ 2 - 128 * X ^ 3 : PowerSeries ℚ)⁻¹)

lemma OMA.a_eq (m : ℕ) : a m = coeff (m + 1) OMA.A := rfl

lemma OMA.dS : 2 * (1 - 4 * X : ℚ⟦X⟧) * d⁄dX ℚ S = (-4 : ℚ⟦X⟧) * S := by
  have E := congrArg (d⁄dX ℚ) OMA.S_sq
  have hR : R = (1 - 4 * X : ℚ⟦X⟧) := rfl
  have h2 := OMA.S_sq
  rw [hR] at E h2
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination S * E - (2 * d⁄dX ℚ S) * h2

lemma OMA.AD : OMA.A * (2 - 24 * X + 96 * X ^ 2 - 128 * X ^ 3 : PowerSeries ℚ) = (-1 + 12 * X - 52 * X ^ 2 + 88 * X ^ 3 - 32 * X ^ 4 + (1 - 10 * X + 34 * X ^ 2 - 36 * X ^ 3) * S) := by
  unfold OMA.A
  have hD : constantCoeff (2 - 24 * X + 96 * X ^ 2 - 128 * X ^ 3 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
    norm_num
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hD, mul_one]

lemma OMA.dAD : (2 - 24 * X + 96 * X ^ 2 - 128 * X ^ 3 : ℚ⟦X⟧) * d⁄dX ℚ OMA.A + OMA.A * (-24 + 192 * X - 384 * X ^ 2 : ℚ⟦X⟧)
    = (12 - 104 * X + 264 * X ^ 2 - 128 * X ^ 3 : ℚ⟦X⟧) + (-10 + 68 * X - 108 * X ^ 2 : ℚ⟦X⟧) * S + (1 - 10 * X + 34 * X ^ 2 - 36 * X ^ 3 : ℚ⟦X⟧) * d⁄dX ℚ S := by
  have E := congrArg (d⁄dX ℚ) OMA.AD
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination E

lemma OMA.fo : (4 - 104 * X + 1160 * X ^ 2 - 7184 * X ^ 3 + 26624 * X ^ 4 - 58880 * X ^ 5 + 71680 * X ^ 6 - 36864 * X ^ 7 : ℚ⟦X⟧) * d⁄dX ℚ OMA.A + (-32 * X + 544 * X ^ 2 - 3744 * X ^ 3 + 13184 * X ^ 4 - 24064 * X ^ 5 + 18432 * X ^ 6 : ℚ⟦X⟧) * OMA.A = (16 * X ^ 3 - 96 * X ^ 4 - 256 * X ^ 5 + 2688 * X ^ 6 - 4608 * X ^ 7 : ℚ⟦X⟧) := by
  have F3 := OMA.AD
  have F4 := OMA.dAD
  have hS := OMA.dS
  linear_combination (2 * (1 - 4 * X : ℚ⟦X⟧) * (1 - 10 * X + 34 * X ^ 2 - 36 * X ^ 3 : ℚ⟦X⟧)) * F4
    - (2 * (1 - 4 * X : ℚ⟦X⟧) * (-10 + 68 * X - 108 * X ^ 2 : ℚ⟦X⟧) + (1 - 10 * X + 34 * X ^ 2 - 36 * X ^ 3 : ℚ⟦X⟧) * (-4 : ℚ⟦X⟧)) * F3 + ((1 - 10 * X + 34 * X ^ 2 - 36 * X ^ 3 : ℚ⟦X⟧) * (1 - 10 * X + 34 * X ^ 2 - 36 * X ^ 3 : ℚ⟦X⟧)) * hS

lemma OMA.fo2 : (4 - 104 * X + 1160 * X ^ 2 - 7184 * X ^ 3 + 26624 * X ^ 4 - 58880 * X ^ 5 + 71680 * X ^ 6 - 36864 * X ^ 7 : ℚ⟦X⟧) * d⁄dX ℚ (d⁄dX ℚ OMA.A) + ((-104 + 2320 * X - 21552 * X ^ 2 + 106496 * X ^ 3 - 294400 * X ^ 4 + 430080 * X ^ 5 - 258048 * X ^ 6 : ℚ⟦X⟧) + (-32 * X + 544 * X ^ 2 - 3744 * X ^ 3 + 13184 * X ^ 4 - 24064 * X ^ 5 + 18432 * X ^ 6 : ℚ⟦X⟧)) * d⁄dX ℚ OMA.A
    + (-32 + 1088 * X - 11232 * X ^ 2 + 52736 * X ^ 3 - 120320 * X ^ 4 + 110592 * X ^ 5 : ℚ⟦X⟧) * OMA.A = (48 * X ^ 2 - 384 * X ^ 3 - 1280 * X ^ 4 + 16128 * X ^ 5 - 32256 * X ^ 6 : ℚ⟦X⟧) := by
  have E := congrArg (d⁄dX ℚ) OMA.fo
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination E

lemma OMA.th2 : X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A) = X * X * d⁄dX ℚ (d⁄dX ℚ OMA.A) + X * d⁄dX ℚ OMA.A := by
  rw [Derivation.leibniz]
  simp only [derivative_X, smul_eq_mul]
  ring

lemma OMA.ode : (1 : ℚ⟦X⟧) * ((-25 - 25 * X + 1188 * X ^ 2 - 1904 * X ^ 3 - 3392 * X ^ 4 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))
    + (3339 - 47230 * X + 260102 * X ^ 2 - 635296 * X ^ 3 + 547488 * X ^ 4 : ℚ⟦X⟧) * (X * d⁄dX ℚ OMA.A)
    + (-26312 * X ^ 2 + 143232 * X ^ 3 - 272896 * X ^ 4 : ℚ⟦X⟧) * OMA.A) - (12956 * X ^ 4 + 67800 * X ^ 5 : ℚ⟦X⟧) = 0 := by
  have h1' := OMA.fo
  have h2' := OMA.fo2
  have h3' := OMA.th2
  have key : ((4 - 104 * X + 1160 * X ^ 2 - 7184 * X ^ 3 + 26624 * X ^ 4 - 58880 * X ^ 5 + 71680 * X ^ 6 - 36864 * X ^ 7 : ℚ⟦X⟧) * (4 - 104 * X + 1160 * X ^ 2 - 7184 * X ^ 3 + 26624 * X ^ 4 - 58880 * X ^ 5 + 71680 * X ^ 6 - 36864 * X ^ 7 : ℚ⟦X⟧))
      * ((1 : ℚ⟦X⟧) * ((-25 - 25 * X + 1188 * X ^ 2 - 1904 * X ^ 3 - 3392 * X ^ 4 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))
    + (3339 - 47230 * X + 260102 * X ^ 2 - 635296 * X ^ 3 + 547488 * X ^ 4 : ℚ⟦X⟧) * (X * d⁄dX ℚ OMA.A)
    + (-26312 * X ^ 2 + 143232 * X ^ 3 - 272896 * X ^ 4 : ℚ⟦X⟧) * OMA.A) - (12956 * X ^ 4 + 67800 * X ^ 5 : ℚ⟦X⟧)) = 0 := by
    linear_combination
      ((1 : ℚ⟦X⟧) * (-25 - 25 * X + 1188 * X ^ 2 - 1904 * X ^ 3 - 3392 * X ^ 4 : ℚ⟦X⟧) * (4 - 104 * X + 1160 * X ^ 2 - 7184 * X ^ 3 + 26624 * X ^ 4 - 58880 * X ^ 5 + 71680 * X ^ 6 - 36864 * X ^ 7 : ℚ⟦X⟧) * (4 - 104 * X + 1160 * X ^ 2 - 7184 * X ^ 3 + 26624 * X ^ 4 - 58880 * X ^ 5 + 71680 * X ^ 6 - 36864 * X ^ 7 : ℚ⟦X⟧)) * h3'
        + ((1 : ℚ⟦X⟧) * (-25 - 25 * X + 1188 * X ^ 2 - 1904 * X ^ 3 - 3392 * X ^ 4 : ℚ⟦X⟧) * X ^ 2 * (4 - 104 * X + 1160 * X ^ 2 - 7184 * X ^ 3 + 26624 * X ^ 4 - 58880 * X ^ 5 + 71680 * X ^ 6 - 36864 * X ^ 7 : ℚ⟦X⟧)) * h2'
        + ((1 : ℚ⟦X⟧) * (13256 * X - 536276 * X ^ 2 + 9858520 * X ^ 3 - 108690984 * X ^ 4 + 798380880 * X ^ 5 - 4101591296 * X ^ 6 + 15034115328 * X ^ 7 - 39305134080 * X ^ 8 + 71800385536 * X ^ 9 - 87239229440 * X ^ 10 + 63411519488 * X ^ 11 - 20870332416 * X ^ 12 : ℚ⟦X⟧)) * h1'
  have hc1 : (4 - 104 * X + 1160 * X ^ 2 - 7184 * X ^ 3 + 26624 * X ^ 4 - 58880 * X ^ 5 + 71680 * X ^ 6 - 36864 * X ^ 7 : ℚ⟦X⟧) ≠ 0 := by
    have e : (4 - 104 * X + 1160 * X ^ 2 - 7184 * X ^ 3 + 26624 * X ^ 4 - 58880 * X ^ 5 + 71680 * X ^ 6 - 36864 * X ^ 7 : ℚ⟦X⟧) = 2 * (1 - 4 * X : ℚ⟦X⟧) * (2 - 24 * X + 96 * X ^ 2 - 128 * X ^ 3 : ℚ⟦X⟧) * (X ^ 0 * (1 - 10 * X + 34 * X ^ 2 - 36 * X ^ 3 : ℚ⟦X⟧)) := by ring
    rw [e]
    have h1 : (2 * (1 - 4 * X : ℚ⟦X⟧) : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    have h2 : (2 - 24 * X + 96 * X ^ 2 - 128 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    have h3 : (1 - 10 * X + 34 * X ^ 2 - 36 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    exact mul_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero (pow_ne_zero _ X_ne_zero) h3)
  exact (mul_eq_zero.mp key).resolve_left (mul_ne_zero hc1 hc1)

theorem OMA.solution : type_of% @OMA.S_oeis_a217711.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  have hexp : C (-25 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (-25 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (1188 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (-1904 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (-3392 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (3339 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ OMA.A))
      + C (-47230 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ OMA.A))
      + C (260102 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ OMA.A))
      + C (-635296 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ OMA.A))
      + C (547488 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ OMA.A))
      + C (-26312 : ℚ) * (X ^ 2 * OMA.A)
      + C (143232 : ℚ) * (X ^ 3 * OMA.A)
      + C (-272896 : ℚ) * (X ^ 4 * OMA.A)
      = C (12956 : ℚ) * X ^ 4 + C (67800 : ℚ) * X ^ 5 := by
    have h := OMA.ode
    simp only [map_neg, map_ofNat, map_one]
    linear_combination h
  have hc := congrArg (coeff (k + 8)) hexp
  have s0 : coeff (k + 8) (C (-25 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-25 : ℚ) * (((k + 8 : ℕ) : ℚ) * (((k + 8 : ℕ) : ℚ) * coeff (k + 8) OMA.A)) :=
    OMA.cXtt _ 0 _ (k + 8) _ (by omega)
  have s1 : coeff (k + 8) (C (-25 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-25 : ℚ) * (((k + 7 : ℕ) : ℚ) * (((k + 7 : ℕ) : ℚ) * coeff (k + 7) OMA.A)) :=
    OMA.cXtt _ 1 _ (k + 7) _ (by omega)
  have s2 : coeff (k + 8) (C (1188 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (1188 : ℚ) * (((k + 6 : ℕ) : ℚ) * (((k + 6 : ℕ) : ℚ) * coeff (k + 6) OMA.A)) :=
    OMA.cXtt _ 2 _ (k + 6) _ (by omega)
  have s3 : coeff (k + 8) (C (-1904 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-1904 : ℚ) * (((k + 5 : ℕ) : ℚ) * (((k + 5 : ℕ) : ℚ) * coeff (k + 5) OMA.A)) :=
    OMA.cXtt _ 3 _ (k + 5) _ (by omega)
  have s4 : coeff (k + 8) (C (-3392 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-3392 : ℚ) * (((k + 4 : ℕ) : ℚ) * (((k + 4 : ℕ) : ℚ) * coeff (k + 4) OMA.A)) :=
    OMA.cXtt _ 4 _ (k + 4) _ (by omega)
  have t0 : coeff (k + 8) (C (3339 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ OMA.A)))
      = (3339 : ℚ) * (((k + 8 : ℕ) : ℚ) * coeff (k + 8) OMA.A) :=
    OMA.cXt _ 0 _ (k + 8) _ (by omega)
  have t1 : coeff (k + 8) (C (-47230 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ OMA.A)))
      = (-47230 : ℚ) * (((k + 7 : ℕ) : ℚ) * coeff (k + 7) OMA.A) :=
    OMA.cXt _ 1 _ (k + 7) _ (by omega)
  have t2 : coeff (k + 8) (C (260102 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ OMA.A)))
      = (260102 : ℚ) * (((k + 6 : ℕ) : ℚ) * coeff (k + 6) OMA.A) :=
    OMA.cXt _ 2 _ (k + 6) _ (by omega)
  have t3 : coeff (k + 8) (C (-635296 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ OMA.A)))
      = (-635296 : ℚ) * (((k + 5 : ℕ) : ℚ) * coeff (k + 5) OMA.A) :=
    OMA.cXt _ 3 _ (k + 5) _ (by omega)
  have t4 : coeff (k + 8) (C (547488 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ OMA.A)))
      = (547488 : ℚ) * (((k + 4 : ℕ) : ℚ) * coeff (k + 4) OMA.A) :=
    OMA.cXt _ 4 _ (k + 4) _ (by omega)
  have f2 : coeff (k + 8) (C (-26312 : ℚ) * (X ^ 2 * OMA.A))
      = (-26312 : ℚ) * coeff (k + 6) OMA.A := OMA.cXf _ 2 _ (k + 6) _ (by omega)
  have f3 : coeff (k + 8) (C (143232 : ℚ) * (X ^ 3 * OMA.A))
      = (143232 : ℚ) * coeff (k + 5) OMA.A := OMA.cXf _ 3 _ (k + 5) _ (by omega)
  have f4 : coeff (k + 8) (C (-272896 : ℚ) * (X ^ 4 * OMA.A))
      = (-272896 : ℚ) * coeff (k + 4) OMA.A := OMA.cXf _ 4 _ (k + 4) _ (by omega)
  have z4 : coeff (k + 8) (C (12956 : ℚ) * X ^ 4 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 4 _ (by omega)
  have z5 : coeff (k + 8) (C (67800 : ℚ) * X ^ 5 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 5 _ (by omega)
  simp only [map_add, map_zero, s0, s1, s2, s3, s4, t0, t1, t2, t3, t4, f2, f3, f4, z4, z5] at hc
  have e0 : a (k + 7) = coeff (k + 8) OMA.A := by
    have h : k + 7 + 1 = k + 8 := by omega
    rw [OMA.a_eq, h]
  have e1 : a (k + 7 - 1) = coeff (k + 7) OMA.A := by
    have h : k + 7 - 1 + 1 = k + 7 := by omega
    rw [OMA.a_eq, h]
  have e2 : a (k + 7 - 2) = coeff (k + 6) OMA.A := by
    have h : k + 7 - 2 + 1 = k + 6 := by omega
    rw [OMA.a_eq, h]
  have e3 : a (k + 7 - 3) = coeff (k + 5) OMA.A := by
    have h : k + 7 - 3 + 1 = k + 5 := by omega
    rw [OMA.a_eq, h]
  have e4 : a (k + 7 - 4) = coeff (k + 4) OMA.A := by
    have h : k + 7 - 4 + 1 = k + 4 := by omega
    rw [OMA.a_eq, h]
  rw [e0, e1, e2, e3, e4]
  push_cast at hc ⊢
  linear_combination (1 / 1 : ℚ) * hc
