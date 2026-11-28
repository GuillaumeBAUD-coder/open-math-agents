import OMAStatements.S_oeis_a165540

-- Problem: OEIS A165540. The sequence is given by the generating function
-- A(x) = (P + Q * sqrt(R)) / D with polynomials P, Q, D, R; the conjectured recurrence is the
-- coefficientwise form of a second order linear differential equation for A.
-- Proof. S = sqrt(R) satisfies S^2 = R, hence 2 R S' = R' S. Differentiating A D = P + Q S and
-- eliminating S and S' gives c1 A' + c0 A = c with c1 = 2RDQ, c0 = 2RQD' - (2RQ' + QR')D,
-- c = 2RQP' - (2RQ' + QR')P. Differentiating once more expresses A'' through A' and A, and the
-- operator of the recurrence, b2 (x d/dx)^2 + b1 (x d/dx) + b0, then sends A to a polynomial T.
-- Comparing the coefficients of x^N for N large gives the recurrence.

open OMA.S_oeis_a165540 PowerSeries

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
    ((-2 + 21 * X - 78 * X ^ 2 + 122 * X ^ 3 - 77 * X ^ 4 + 20 * X ^ 5 + (2 - 17 * X + 48 * X ^ 2 - 50 * X ^ 3 + 13 * X ^ 4) * S)
      * (2 - 14 * X + 26 * X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

lemma OMA.a_eq (m : ℕ) : a m = coeff (m + 3) OMA.A := rfl

lemma OMA.dS : 2 * (1 - 4 * X : ℚ⟦X⟧) * d⁄dX ℚ S = (-4 : ℚ⟦X⟧) * S := by
  have E := congrArg (d⁄dX ℚ) OMA.S_sq
  have hR : R = (1 - 4 * X : ℚ⟦X⟧) := rfl
  have h2 := OMA.S_sq
  rw [hR] at E h2
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination S * E - (2 * d⁄dX ℚ S) * h2

lemma OMA.AD : OMA.A * (2 - 14 * X + 26 * X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ) = (-2 + 21 * X - 78 * X ^ 2 + 122 * X ^ 3 - 77 * X ^ 4 + 20 * X ^ 5 + (2 - 17 * X + 48 * X ^ 2 - 50 * X ^ 3 + 13 * X ^ 4) * S) := by
  unfold OMA.A
  have hD : constantCoeff (2 - 14 * X + 26 * X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
    norm_num
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hD, mul_one]

lemma OMA.dAD : (2 - 14 * X + 26 * X ^ 2 - 8 * X ^ 3 : ℚ⟦X⟧) * d⁄dX ℚ OMA.A + OMA.A * (-14 + 52 * X - 24 * X ^ 2 : ℚ⟦X⟧)
    = (21 - 156 * X + 366 * X ^ 2 - 308 * X ^ 3 + 100 * X ^ 4 : ℚ⟦X⟧) + (-17 + 96 * X - 150 * X ^ 2 + 52 * X ^ 3 : ℚ⟦X⟧) * S + (2 - 17 * X + 48 * X ^ 2 - 50 * X ^ 3 + 13 * X ^ 4 : ℚ⟦X⟧) * d⁄dX ℚ S := by
  have E := congrArg (d⁄dX ℚ) OMA.AD
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination E

lemma OMA.fo : (8 - 156 * X + 1268 * X ^ 2 - 5548 * X ^ 3 + 14060 * X ^ 4 - 20612 * X ^ 5 + 16404 * X ^ 6 - 6112 * X ^ 7 + 832 * X ^ 8 : ℚ⟦X⟧) * d⁄dX ℚ OMA.A + (28 - 472 * X + 3212 * X ^ 2 - 11240 * X ^ 3 + 21220 * X ^ 4 - 20512 * X ^ 5 + 8568 * X ^ 6 - 1248 * X ^ 7 : ℚ⟦X⟧) * OMA.A = (24 * X ^ 2 - 408 * X ^ 3 + 2816 * X ^ 4 - 10048 * X ^ 5 + 19480 * X ^ 6 - 19568 * X ^ 7 + 8516 * X ^ 8 - 1040 * X ^ 9 : ℚ⟦X⟧) := by
  have F3 := OMA.AD
  have F4 := OMA.dAD
  have hS := OMA.dS
  linear_combination (2 * (1 - 4 * X : ℚ⟦X⟧) * (2 - 17 * X + 48 * X ^ 2 - 50 * X ^ 3 + 13 * X ^ 4 : ℚ⟦X⟧)) * F4
    - (2 * (1 - 4 * X : ℚ⟦X⟧) * (-17 + 96 * X - 150 * X ^ 2 + 52 * X ^ 3 : ℚ⟦X⟧) + (2 - 17 * X + 48 * X ^ 2 - 50 * X ^ 3 + 13 * X ^ 4 : ℚ⟦X⟧) * (-4 : ℚ⟦X⟧)) * F3 + ((2 - 17 * X + 48 * X ^ 2 - 50 * X ^ 3 + 13 * X ^ 4 : ℚ⟦X⟧) * (2 - 17 * X + 48 * X ^ 2 - 50 * X ^ 3 + 13 * X ^ 4 : ℚ⟦X⟧)) * hS

lemma OMA.fo2 : (8 - 156 * X + 1268 * X ^ 2 - 5548 * X ^ 3 + 14060 * X ^ 4 - 20612 * X ^ 5 + 16404 * X ^ 6 - 6112 * X ^ 7 + 832 * X ^ 8 : ℚ⟦X⟧) * d⁄dX ℚ (d⁄dX ℚ OMA.A) + ((-156 + 2536 * X - 16644 * X ^ 2 + 56240 * X ^ 3 - 103060 * X ^ 4 + 98424 * X ^ 5 - 42784 * X ^ 6 + 6656 * X ^ 7 : ℚ⟦X⟧) + (28 - 472 * X + 3212 * X ^ 2 - 11240 * X ^ 3 + 21220 * X ^ 4 - 20512 * X ^ 5 + 8568 * X ^ 6 - 1248 * X ^ 7 : ℚ⟦X⟧)) * d⁄dX ℚ OMA.A
    + (-472 + 6424 * X - 33720 * X ^ 2 + 84880 * X ^ 3 - 102560 * X ^ 4 + 51408 * X ^ 5 - 8736 * X ^ 6 : ℚ⟦X⟧) * OMA.A = (48 * X - 1224 * X ^ 2 + 11264 * X ^ 3 - 50240 * X ^ 4 + 116880 * X ^ 5 - 136976 * X ^ 6 + 68128 * X ^ 7 - 9360 * X ^ 8 : ℚ⟦X⟧) := by
  have E := congrArg (d⁄dX ℚ) OMA.fo
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination E

lemma OMA.th2 : X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A) = X * X * d⁄dX ℚ (d⁄dX ℚ OMA.A) + X * d⁄dX ℚ OMA.A := by
  rw [Derivation.leibniz]
  simp only [derivative_X, smul_eq_mul]
  ring

lemma OMA.ode : (1 : ℚ⟦X⟧) * ((14681 + 14681 * X - 888761 * X ^ 2 + 3270446 * X ^ 3 - 3817006 * X ^ 4 + 1029912 * X ^ 5 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))
    + (143911 - 2755507 * X + 14549061 * X ^ 2 - 29701670 * X ^ 3 + 23171294 * X ^ 4 - 3969732 * X ^ 5 : ℚ⟦X⟧) * (X * d⁄dX ℚ OMA.A)
    + (555072 * X - 8169958 * X ^ 2 + 26562024 * X ^ 3 - 24791340 * X ^ 4 + 3637296 * X ^ 5 : ℚ⟦X⟧) * OMA.A) - (563862 * X ^ 3 - 6768780 * X ^ 4 + 19419476 * X ^ 5 - 14661846 * X ^ 6 + 456300 * X ^ 7 : ℚ⟦X⟧) = 0 := by
  have h1' := OMA.fo
  have h2' := OMA.fo2
  have h3' := OMA.th2
  have key : ((8 - 156 * X + 1268 * X ^ 2 - 5548 * X ^ 3 + 14060 * X ^ 4 - 20612 * X ^ 5 + 16404 * X ^ 6 - 6112 * X ^ 7 + 832 * X ^ 8 : ℚ⟦X⟧) * (8 - 156 * X + 1268 * X ^ 2 - 5548 * X ^ 3 + 14060 * X ^ 4 - 20612 * X ^ 5 + 16404 * X ^ 6 - 6112 * X ^ 7 + 832 * X ^ 8 : ℚ⟦X⟧))
      * ((1 : ℚ⟦X⟧) * ((14681 + 14681 * X - 888761 * X ^ 2 + 3270446 * X ^ 3 - 3817006 * X ^ 4 + 1029912 * X ^ 5 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))
    + (143911 - 2755507 * X + 14549061 * X ^ 2 - 29701670 * X ^ 3 + 23171294 * X ^ 4 - 3969732 * X ^ 5 : ℚ⟦X⟧) * (X * d⁄dX ℚ OMA.A)
    + (555072 * X - 8169958 * X ^ 2 + 26562024 * X ^ 3 - 24791340 * X ^ 4 + 3637296 * X ^ 5 : ℚ⟦X⟧) * OMA.A) - (563862 * X ^ 3 - 6768780 * X ^ 4 + 19419476 * X ^ 5 - 14661846 * X ^ 6 + 456300 * X ^ 7 : ℚ⟦X⟧)) = 0 := by
    linear_combination
      ((1 : ℚ⟦X⟧) * (14681 + 14681 * X - 888761 * X ^ 2 + 3270446 * X ^ 3 - 3817006 * X ^ 4 + 1029912 * X ^ 5 : ℚ⟦X⟧) * (8 - 156 * X + 1268 * X ^ 2 - 5548 * X ^ 3 + 14060 * X ^ 4 - 20612 * X ^ 5 + 16404 * X ^ 6 - 6112 * X ^ 7 + 832 * X ^ 8 : ℚ⟦X⟧) * (8 - 156 * X + 1268 * X ^ 2 - 5548 * X ^ 3 + 14060 * X ^ 4 - 20612 * X ^ 5 + 16404 * X ^ 6 - 6112 * X ^ 7 + 832 * X ^ 8 : ℚ⟦X⟧)) * h3'
        + ((1 : ℚ⟦X⟧) * (14681 + 14681 * X - 888761 * X ^ 2 + 3270446 * X ^ 3 - 3817006 * X ^ 4 + 1029912 * X ^ 5 : ℚ⟦X⟧) * X ^ 2 * (8 - 156 * X + 1268 * X ^ 2 - 5548 * X ^ 3 + 14060 * X ^ 4 - 20612 * X ^ 5 + 16404 * X ^ 6 - 6112 * X ^ 7 + 832 * X ^ 8 : ℚ⟦X⟧)) * h2'
        + ((1 : ℚ⟦X⟧) * (1268736 * X - 44787792 * X ^ 2 + 709523496 * X ^ 3 - 6644560176 * X ^ 4 + 40824841800 * X ^ 5 - 172785602808 * X ^ 6 + 514790218296 * X ^ 7 - 1084167752808 * X ^ 8 + 1597119663888 * X ^ 9 - 1603640413800 * X ^ 10 + 1049382890256 * X ^ 11 - 417040746912 * X ^ 12 + 89952784896 * X ^ 13 - 8015694336 * X ^ 14 : ℚ⟦X⟧)) * h1'
  have hc1 : (8 - 156 * X + 1268 * X ^ 2 - 5548 * X ^ 3 + 14060 * X ^ 4 - 20612 * X ^ 5 + 16404 * X ^ 6 - 6112 * X ^ 7 + 832 * X ^ 8 : ℚ⟦X⟧) ≠ 0 := by
    have e : (8 - 156 * X + 1268 * X ^ 2 - 5548 * X ^ 3 + 14060 * X ^ 4 - 20612 * X ^ 5 + 16404 * X ^ 6 - 6112 * X ^ 7 + 832 * X ^ 8 : ℚ⟦X⟧) = 2 * (1 - 4 * X : ℚ⟦X⟧) * (2 - 14 * X + 26 * X ^ 2 - 8 * X ^ 3 : ℚ⟦X⟧) * (X ^ 0 * (2 - 17 * X + 48 * X ^ 2 - 50 * X ^ 3 + 13 * X ^ 4 : ℚ⟦X⟧)) := by ring
    rw [e]
    have h1 : (2 * (1 - 4 * X : ℚ⟦X⟧) : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    have h2 : (2 - 14 * X + 26 * X ^ 2 - 8 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    have h3 : (2 - 17 * X + 48 * X ^ 2 - 50 * X ^ 3 + 13 * X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    exact mul_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero (pow_ne_zero _ X_ne_zero) h3)
  exact (mul_eq_zero.mp key).resolve_left (mul_ne_zero hc1 hc1)

theorem OMA.solution : type_of% @OMA.S_oeis_a165540.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have hexp : C (14681 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (14681 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (-888761 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (3270446 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (-3817006 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (1029912 : ℚ) * (X ^ 5 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (143911 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ OMA.A))
      + C (-2755507 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ OMA.A))
      + C (14549061 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ OMA.A))
      + C (-29701670 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ OMA.A))
      + C (23171294 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ OMA.A))
      + C (-3969732 : ℚ) * (X ^ 5 * (X * d⁄dX ℚ OMA.A))
      + C (555072 : ℚ) * (X ^ 1 * OMA.A)
      + C (-8169958 : ℚ) * (X ^ 2 * OMA.A)
      + C (26562024 : ℚ) * (X ^ 3 * OMA.A)
      + C (-24791340 : ℚ) * (X ^ 4 * OMA.A)
      + C (3637296 : ℚ) * (X ^ 5 * OMA.A)
      = C (563862 : ℚ) * X ^ 3 + C (-6768780 : ℚ) * X ^ 4 + C (19419476 : ℚ) * X ^ 5 + C (-14661846 : ℚ) * X ^ 6 + C (456300 : ℚ) * X ^ 7 := by
    have h := OMA.ode
    simp only [map_neg, map_ofNat, map_one]
    linear_combination h
  have hc := congrArg (coeff (k + 8)) hexp
  have s0 : coeff (k + 8) (C (14681 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (14681 : ℚ) * (((k + 8 : ℕ) : ℚ) * (((k + 8 : ℕ) : ℚ) * coeff (k + 8) OMA.A)) :=
    OMA.cXtt _ 0 _ (k + 8) _ (by omega)
  have s1 : coeff (k + 8) (C (14681 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (14681 : ℚ) * (((k + 7 : ℕ) : ℚ) * (((k + 7 : ℕ) : ℚ) * coeff (k + 7) OMA.A)) :=
    OMA.cXtt _ 1 _ (k + 7) _ (by omega)
  have s2 : coeff (k + 8) (C (-888761 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-888761 : ℚ) * (((k + 6 : ℕ) : ℚ) * (((k + 6 : ℕ) : ℚ) * coeff (k + 6) OMA.A)) :=
    OMA.cXtt _ 2 _ (k + 6) _ (by omega)
  have s3 : coeff (k + 8) (C (3270446 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (3270446 : ℚ) * (((k + 5 : ℕ) : ℚ) * (((k + 5 : ℕ) : ℚ) * coeff (k + 5) OMA.A)) :=
    OMA.cXtt _ 3 _ (k + 5) _ (by omega)
  have s4 : coeff (k + 8) (C (-3817006 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-3817006 : ℚ) * (((k + 4 : ℕ) : ℚ) * (((k + 4 : ℕ) : ℚ) * coeff (k + 4) OMA.A)) :=
    OMA.cXtt _ 4 _ (k + 4) _ (by omega)
  have s5 : coeff (k + 8) (C (1029912 : ℚ) * (X ^ 5 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (1029912 : ℚ) * (((k + 3 : ℕ) : ℚ) * (((k + 3 : ℕ) : ℚ) * coeff (k + 3) OMA.A)) :=
    OMA.cXtt _ 5 _ (k + 3) _ (by omega)
  have t0 : coeff (k + 8) (C (143911 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ OMA.A)))
      = (143911 : ℚ) * (((k + 8 : ℕ) : ℚ) * coeff (k + 8) OMA.A) :=
    OMA.cXt _ 0 _ (k + 8) _ (by omega)
  have t1 : coeff (k + 8) (C (-2755507 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ OMA.A)))
      = (-2755507 : ℚ) * (((k + 7 : ℕ) : ℚ) * coeff (k + 7) OMA.A) :=
    OMA.cXt _ 1 _ (k + 7) _ (by omega)
  have t2 : coeff (k + 8) (C (14549061 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ OMA.A)))
      = (14549061 : ℚ) * (((k + 6 : ℕ) : ℚ) * coeff (k + 6) OMA.A) :=
    OMA.cXt _ 2 _ (k + 6) _ (by omega)
  have t3 : coeff (k + 8) (C (-29701670 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ OMA.A)))
      = (-29701670 : ℚ) * (((k + 5 : ℕ) : ℚ) * coeff (k + 5) OMA.A) :=
    OMA.cXt _ 3 _ (k + 5) _ (by omega)
  have t4 : coeff (k + 8) (C (23171294 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ OMA.A)))
      = (23171294 : ℚ) * (((k + 4 : ℕ) : ℚ) * coeff (k + 4) OMA.A) :=
    OMA.cXt _ 4 _ (k + 4) _ (by omega)
  have t5 : coeff (k + 8) (C (-3969732 : ℚ) * (X ^ 5 * (X * d⁄dX ℚ OMA.A)))
      = (-3969732 : ℚ) * (((k + 3 : ℕ) : ℚ) * coeff (k + 3) OMA.A) :=
    OMA.cXt _ 5 _ (k + 3) _ (by omega)
  have f1 : coeff (k + 8) (C (555072 : ℚ) * (X ^ 1 * OMA.A))
      = (555072 : ℚ) * coeff (k + 7) OMA.A := OMA.cXf _ 1 _ (k + 7) _ (by omega)
  have f2 : coeff (k + 8) (C (-8169958 : ℚ) * (X ^ 2 * OMA.A))
      = (-8169958 : ℚ) * coeff (k + 6) OMA.A := OMA.cXf _ 2 _ (k + 6) _ (by omega)
  have f3 : coeff (k + 8) (C (26562024 : ℚ) * (X ^ 3 * OMA.A))
      = (26562024 : ℚ) * coeff (k + 5) OMA.A := OMA.cXf _ 3 _ (k + 5) _ (by omega)
  have f4 : coeff (k + 8) (C (-24791340 : ℚ) * (X ^ 4 * OMA.A))
      = (-24791340 : ℚ) * coeff (k + 4) OMA.A := OMA.cXf _ 4 _ (k + 4) _ (by omega)
  have f5 : coeff (k + 8) (C (3637296 : ℚ) * (X ^ 5 * OMA.A))
      = (3637296 : ℚ) * coeff (k + 3) OMA.A := OMA.cXf _ 5 _ (k + 3) _ (by omega)
  have z3 : coeff (k + 8) (C (563862 : ℚ) * X ^ 3 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 3 _ (by omega)
  have z4 : coeff (k + 8) (C (-6768780 : ℚ) * X ^ 4 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 4 _ (by omega)
  have z5 : coeff (k + 8) (C (19419476 : ℚ) * X ^ 5 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 5 _ (by omega)
  have z6 : coeff (k + 8) (C (-14661846 : ℚ) * X ^ 6 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 6 _ (by omega)
  have z7 : coeff (k + 8) (C (456300 : ℚ) * X ^ 7 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 7 _ (by omega)
  simp only [map_add, map_zero, s0, s1, s2, s3, s4, s5, t0, t1, t2, t3, t4, t5, f1, f2, f3, f4, f5, z3, z4, z5, z6, z7] at hc
  have e0 : a (k + 5) = coeff (k + 8) OMA.A := by
    have h : k + 5 + 3 = k + 8 := by omega
    rw [OMA.a_eq, h]
  have e1 : a (k + 5 - 1) = coeff (k + 7) OMA.A := by
    have h : k + 5 - 1 + 3 = k + 7 := by omega
    rw [OMA.a_eq, h]
  have e2 : a (k + 5 - 2) = coeff (k + 6) OMA.A := by
    have h : k + 5 - 2 + 3 = k + 6 := by omega
    rw [OMA.a_eq, h]
  have e3 : a (k + 5 - 3) = coeff (k + 5) OMA.A := by
    have h : k + 5 - 3 + 3 = k + 5 := by omega
    rw [OMA.a_eq, h]
  have e4 : a (k + 5 - 4) = coeff (k + 4) OMA.A := by
    have h : k + 5 - 4 + 3 = k + 4 := by omega
    rw [OMA.a_eq, h]
  have e5 : a (k + 5 - 5) = coeff (k + 3) OMA.A := by
    have h : k + 5 - 5 + 3 = k + 3 := by omega
    rw [OMA.a_eq, h]
  rw [e0, e1, e2, e3, e4, e5]
  push_cast at hc ⊢
  linear_combination (1 / 1 : ℚ) * hc
