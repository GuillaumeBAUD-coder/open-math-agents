import OMAStatements.S_oeis_a228771

-- Problem: OEIS A228771. The sequence is given by the generating function
-- A(x) = (P + Q * sqrt(R)) / D with polynomials P, Q, D, R; the conjectured recurrence is the
-- coefficientwise form of a second order linear differential equation for A.
-- Proof. S = sqrt(R) satisfies S^2 = R, hence 2 R S' = R' S. Differentiating A D = P + Q S and
-- eliminating S and S' gives c1 A' + c0 A = c with c1 = 2RDQ, c0 = 2RQD' - (2RQ' + QR')D,
-- c = 2RQP' - (2RQ' + QR')P. Differentiating once more expresses A'' through A' and A, and the
-- operator of the recurrence, b2 (x d/dx)^2 + b1 (x d/dx) + b0, then sends A to a polynomial T.
-- Comparing the coefficients of x^N for N large gives the recurrence.

open OMA.S_oeis_a228771 PowerSeries

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
    ((-1 + 9 * X - 27 * X ^ 2 + 35 * X ^ 3 - 28 * X ^ 4 + 8 * X ^ 5 + (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 6 * X ^ 4) * S)
      * (2 - 10 * X + 8 * X ^ 2 : PowerSeries ℚ)⁻¹)

lemma OMA.a_eq (m : ℕ) : a m = coeff (m + 2) OMA.A := rfl

lemma OMA.dS : 2 * (1 - 4 * X : ℚ⟦X⟧) * d⁄dX ℚ S = (-4 : ℚ⟦X⟧) * S := by
  have E := congrArg (d⁄dX ℚ) OMA.S_sq
  have hR : R = (1 - 4 * X : ℚ⟦X⟧) := rfl
  have h2 := OMA.S_sq
  rw [hR] at E h2
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination S * E - (2 * d⁄dX ℚ S) * h2

lemma OMA.AD : OMA.A * (2 - 10 * X + 8 * X ^ 2 : PowerSeries ℚ) = (-1 + 9 * X - 27 * X ^ 2 + 35 * X ^ 3 - 28 * X ^ 4 + 8 * X ^ 5 + (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 6 * X ^ 4) * S) := by
  unfold OMA.A
  have hD : constantCoeff (2 - 10 * X + 8 * X ^ 2 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
    norm_num
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hD, mul_one]

lemma OMA.dAD : (2 - 10 * X + 8 * X ^ 2 : ℚ⟦X⟧) * d⁄dX ℚ OMA.A + OMA.A * (-10 + 16 * X : ℚ⟦X⟧)
    = (9 - 54 * X + 105 * X ^ 2 - 112 * X ^ 3 + 40 * X ^ 4 : ℚ⟦X⟧) + (-7 + 30 * X - 39 * X ^ 2 + 24 * X ^ 3 : ℚ⟦X⟧) * S + (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 6 * X ^ 4 : ℚ⟦X⟧) * d⁄dX ℚ S := by
  have E := congrArg (d⁄dX ℚ) OMA.AD
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination E

lemma OMA.fo : (4 - 64 * X + 408 * X ^ 2 - 1328 * X ^ 3 + 2380 * X ^ 4 - 2424 * X ^ 5 + 1408 * X ^ 6 - 384 * X ^ 7 : ℚ⟦X⟧) * d⁄dX ℚ OMA.A + (16 - 216 * X + 1128 * X ^ 2 - 2920 * X ^ 3 + 4080 * X ^ 4 - 3120 * X ^ 5 + 960 * X ^ 6 : ℚ⟦X⟧) * OMA.A = (12 * X ^ 2 - 160 * X ^ 3 + 828 * X ^ 4 - 2064 * X ^ 5 + 2576 * X ^ 6 - 1752 * X ^ 7 + 672 * X ^ 8 - 192 * X ^ 9 : ℚ⟦X⟧) := by
  have F3 := OMA.AD
  have F4 := OMA.dAD
  have hS := OMA.dS
  linear_combination (2 * (1 - 4 * X : ℚ⟦X⟧) * (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 6 * X ^ 4 : ℚ⟦X⟧)) * F4
    - (2 * (1 - 4 * X : ℚ⟦X⟧) * (-7 + 30 * X - 39 * X ^ 2 + 24 * X ^ 3 : ℚ⟦X⟧) + (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 6 * X ^ 4 : ℚ⟦X⟧) * (-4 : ℚ⟦X⟧)) * F3 + ((1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 6 * X ^ 4 : ℚ⟦X⟧) * (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 6 * X ^ 4 : ℚ⟦X⟧)) * hS

lemma OMA.fo2 : (4 - 64 * X + 408 * X ^ 2 - 1328 * X ^ 3 + 2380 * X ^ 4 - 2424 * X ^ 5 + 1408 * X ^ 6 - 384 * X ^ 7 : ℚ⟦X⟧) * d⁄dX ℚ (d⁄dX ℚ OMA.A) + ((-64 + 816 * X - 3984 * X ^ 2 + 9520 * X ^ 3 - 12120 * X ^ 4 + 8448 * X ^ 5 - 2688 * X ^ 6 : ℚ⟦X⟧) + (16 - 216 * X + 1128 * X ^ 2 - 2920 * X ^ 3 + 4080 * X ^ 4 - 3120 * X ^ 5 + 960 * X ^ 6 : ℚ⟦X⟧)) * d⁄dX ℚ OMA.A
    + (-216 + 2256 * X - 8760 * X ^ 2 + 16320 * X ^ 3 - 15600 * X ^ 4 + 5760 * X ^ 5 : ℚ⟦X⟧) * OMA.A = (24 * X - 480 * X ^ 2 + 3312 * X ^ 3 - 10320 * X ^ 4 + 15456 * X ^ 5 - 12264 * X ^ 6 + 5376 * X ^ 7 - 1728 * X ^ 8 : ℚ⟦X⟧) := by
  have E := congrArg (d⁄dX ℚ) OMA.fo
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination E

lemma OMA.th2 : X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A) = X * X * d⁄dX ℚ (d⁄dX ℚ OMA.A) + X * d⁄dX ℚ OMA.A := by
  rw [Derivation.leibniz]
  simp only [derivative_X, smul_eq_mul]
  ring

lemma OMA.ode : (1 : ℚ⟦X⟧) * ((-652 - 652 * X + 72365 * X ^ 2 - 410045 * X ^ 3 + 808312 * X ^ 4 - 469328 * X ^ 5 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))
    + (68623 - 724121 * X + 2561380 * X ^ 2 - 3229054 * X ^ 3 + 639098 * X ^ 4 + 285176 * X ^ 5 : ℚ⟦X⟧) * (X * d⁄dX ℚ OMA.A)
    + (271884 * X - 2215470 * X ^ 2 + 5610000 * X ^ 3 - 4991220 * X ^ 4 + 2220360 * X ^ 5 : ℚ⟦X⟧) * OMA.A) - (200001 * X ^ 3 - 1642287 * X ^ 4 + 4465368 * X ^ 5 - 4015548 * X ^ 6 + 2145732 * X ^ 7 - 1148064 * X ^ 8 : ℚ⟦X⟧) = 0 := by
  have h1' := OMA.fo
  have h2' := OMA.fo2
  have h3' := OMA.th2
  have key : ((4 - 64 * X + 408 * X ^ 2 - 1328 * X ^ 3 + 2380 * X ^ 4 - 2424 * X ^ 5 + 1408 * X ^ 6 - 384 * X ^ 7 : ℚ⟦X⟧) * (4 - 64 * X + 408 * X ^ 2 - 1328 * X ^ 3 + 2380 * X ^ 4 - 2424 * X ^ 5 + 1408 * X ^ 6 - 384 * X ^ 7 : ℚ⟦X⟧))
      * ((1 : ℚ⟦X⟧) * ((-652 - 652 * X + 72365 * X ^ 2 - 410045 * X ^ 3 + 808312 * X ^ 4 - 469328 * X ^ 5 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))
    + (68623 - 724121 * X + 2561380 * X ^ 2 - 3229054 * X ^ 3 + 639098 * X ^ 4 + 285176 * X ^ 5 : ℚ⟦X⟧) * (X * d⁄dX ℚ OMA.A)
    + (271884 * X - 2215470 * X ^ 2 + 5610000 * X ^ 3 - 4991220 * X ^ 4 + 2220360 * X ^ 5 : ℚ⟦X⟧) * OMA.A) - (200001 * X ^ 3 - 1642287 * X ^ 4 + 4465368 * X ^ 5 - 4015548 * X ^ 6 + 2145732 * X ^ 7 - 1148064 * X ^ 8 : ℚ⟦X⟧)) = 0 := by
    linear_combination
      ((1 : ℚ⟦X⟧) * (-652 - 652 * X + 72365 * X ^ 2 - 410045 * X ^ 3 + 808312 * X ^ 4 - 469328 * X ^ 5 : ℚ⟦X⟧) * (4 - 64 * X + 408 * X ^ 2 - 1328 * X ^ 3 + 2380 * X ^ 4 - 2424 * X ^ 5 + 1408 * X ^ 6 - 384 * X ^ 7 : ℚ⟦X⟧) * (4 - 64 * X + 408 * X ^ 2 - 1328 * X ^ 3 + 2380 * X ^ 4 - 2424 * X ^ 5 + 1408 * X ^ 6 - 384 * X ^ 7 : ℚ⟦X⟧)) * h3'
        + ((1 : ℚ⟦X⟧) * (-652 - 652 * X + 72365 * X ^ 2 - 410045 * X ^ 3 + 808312 * X ^ 4 - 469328 * X ^ 5 : ℚ⟦X⟧) * X ^ 2 * (4 - 64 * X + 408 * X ^ 2 - 1328 * X ^ 3 + 2380 * X ^ 4 - 2424 * X ^ 5 + 1408 * X ^ 6 - 384 * X ^ 7 : ℚ⟦X⟧)) * h2'
        + ((1 : ℚ⟦X⟧) * (271884 * X - 7280532 * X ^ 2 + 85012524 * X ^ 3 - 567086340 * X ^ 4 + 2376869388 * X ^ 5 - 6474896508 * X ^ 6 + 11397937812 * X ^ 7 - 12208534572 * X ^ 8 + 6138482280 * X ^ 9 + 1824146688 * X ^ 10 - 4906889472 * X ^ 11 + 3082251264 * X ^ 12 - 740284416 * X ^ 13 : ℚ⟦X⟧)) * h1'
  have hc1 : (4 - 64 * X + 408 * X ^ 2 - 1328 * X ^ 3 + 2380 * X ^ 4 - 2424 * X ^ 5 + 1408 * X ^ 6 - 384 * X ^ 7 : ℚ⟦X⟧) ≠ 0 := by
    have e : (4 - 64 * X + 408 * X ^ 2 - 1328 * X ^ 3 + 2380 * X ^ 4 - 2424 * X ^ 5 + 1408 * X ^ 6 - 384 * X ^ 7 : ℚ⟦X⟧) = 2 * (1 - 4 * X : ℚ⟦X⟧) * (2 - 10 * X + 8 * X ^ 2 : ℚ⟦X⟧) * (X ^ 0 * (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 6 * X ^ 4 : ℚ⟦X⟧)) := by ring
    rw [e]
    have h1 : (2 * (1 - 4 * X : ℚ⟦X⟧) : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    have h2 : (2 - 10 * X + 8 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    have h3 : (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 6 * X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    exact mul_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero (pow_ne_zero _ X_ne_zero) h3)
  exact (mul_eq_zero.mp key).resolve_left (mul_ne_zero hc1 hc1)

theorem OMA.solution : type_of% @OMA.S_oeis_a228771.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  have hexp : C (-652 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (-652 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (72365 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (-410045 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (808312 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (-469328 : ℚ) * (X ^ 5 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (68623 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ OMA.A))
      + C (-724121 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ OMA.A))
      + C (2561380 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ OMA.A))
      + C (-3229054 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ OMA.A))
      + C (639098 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ OMA.A))
      + C (285176 : ℚ) * (X ^ 5 * (X * d⁄dX ℚ OMA.A))
      + C (271884 : ℚ) * (X ^ 1 * OMA.A)
      + C (-2215470 : ℚ) * (X ^ 2 * OMA.A)
      + C (5610000 : ℚ) * (X ^ 3 * OMA.A)
      + C (-4991220 : ℚ) * (X ^ 4 * OMA.A)
      + C (2220360 : ℚ) * (X ^ 5 * OMA.A)
      = C (200001 : ℚ) * X ^ 3 + C (-1642287 : ℚ) * X ^ 4 + C (4465368 : ℚ) * X ^ 5 + C (-4015548 : ℚ) * X ^ 6 + C (2145732 : ℚ) * X ^ 7 + C (-1148064 : ℚ) * X ^ 8 := by
    have h := OMA.ode
    simp only [map_neg, map_ofNat, map_one]
    linear_combination h
  have hc := congrArg (coeff (k + 9)) hexp
  have s0 : coeff (k + 9) (C (-652 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-652 : ℚ) * (((k + 9 : ℕ) : ℚ) * (((k + 9 : ℕ) : ℚ) * coeff (k + 9) OMA.A)) :=
    OMA.cXtt _ 0 _ (k + 9) _ (by omega)
  have s1 : coeff (k + 9) (C (-652 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-652 : ℚ) * (((k + 8 : ℕ) : ℚ) * (((k + 8 : ℕ) : ℚ) * coeff (k + 8) OMA.A)) :=
    OMA.cXtt _ 1 _ (k + 8) _ (by omega)
  have s2 : coeff (k + 9) (C (72365 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (72365 : ℚ) * (((k + 7 : ℕ) : ℚ) * (((k + 7 : ℕ) : ℚ) * coeff (k + 7) OMA.A)) :=
    OMA.cXtt _ 2 _ (k + 7) _ (by omega)
  have s3 : coeff (k + 9) (C (-410045 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-410045 : ℚ) * (((k + 6 : ℕ) : ℚ) * (((k + 6 : ℕ) : ℚ) * coeff (k + 6) OMA.A)) :=
    OMA.cXtt _ 3 _ (k + 6) _ (by omega)
  have s4 : coeff (k + 9) (C (808312 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (808312 : ℚ) * (((k + 5 : ℕ) : ℚ) * (((k + 5 : ℕ) : ℚ) * coeff (k + 5) OMA.A)) :=
    OMA.cXtt _ 4 _ (k + 5) _ (by omega)
  have s5 : coeff (k + 9) (C (-469328 : ℚ) * (X ^ 5 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-469328 : ℚ) * (((k + 4 : ℕ) : ℚ) * (((k + 4 : ℕ) : ℚ) * coeff (k + 4) OMA.A)) :=
    OMA.cXtt _ 5 _ (k + 4) _ (by omega)
  have t0 : coeff (k + 9) (C (68623 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ OMA.A)))
      = (68623 : ℚ) * (((k + 9 : ℕ) : ℚ) * coeff (k + 9) OMA.A) :=
    OMA.cXt _ 0 _ (k + 9) _ (by omega)
  have t1 : coeff (k + 9) (C (-724121 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ OMA.A)))
      = (-724121 : ℚ) * (((k + 8 : ℕ) : ℚ) * coeff (k + 8) OMA.A) :=
    OMA.cXt _ 1 _ (k + 8) _ (by omega)
  have t2 : coeff (k + 9) (C (2561380 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ OMA.A)))
      = (2561380 : ℚ) * (((k + 7 : ℕ) : ℚ) * coeff (k + 7) OMA.A) :=
    OMA.cXt _ 2 _ (k + 7) _ (by omega)
  have t3 : coeff (k + 9) (C (-3229054 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ OMA.A)))
      = (-3229054 : ℚ) * (((k + 6 : ℕ) : ℚ) * coeff (k + 6) OMA.A) :=
    OMA.cXt _ 3 _ (k + 6) _ (by omega)
  have t4 : coeff (k + 9) (C (639098 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ OMA.A)))
      = (639098 : ℚ) * (((k + 5 : ℕ) : ℚ) * coeff (k + 5) OMA.A) :=
    OMA.cXt _ 4 _ (k + 5) _ (by omega)
  have t5 : coeff (k + 9) (C (285176 : ℚ) * (X ^ 5 * (X * d⁄dX ℚ OMA.A)))
      = (285176 : ℚ) * (((k + 4 : ℕ) : ℚ) * coeff (k + 4) OMA.A) :=
    OMA.cXt _ 5 _ (k + 4) _ (by omega)
  have f1 : coeff (k + 9) (C (271884 : ℚ) * (X ^ 1 * OMA.A))
      = (271884 : ℚ) * coeff (k + 8) OMA.A := OMA.cXf _ 1 _ (k + 8) _ (by omega)
  have f2 : coeff (k + 9) (C (-2215470 : ℚ) * (X ^ 2 * OMA.A))
      = (-2215470 : ℚ) * coeff (k + 7) OMA.A := OMA.cXf _ 2 _ (k + 7) _ (by omega)
  have f3 : coeff (k + 9) (C (5610000 : ℚ) * (X ^ 3 * OMA.A))
      = (5610000 : ℚ) * coeff (k + 6) OMA.A := OMA.cXf _ 3 _ (k + 6) _ (by omega)
  have f4 : coeff (k + 9) (C (-4991220 : ℚ) * (X ^ 4 * OMA.A))
      = (-4991220 : ℚ) * coeff (k + 5) OMA.A := OMA.cXf _ 4 _ (k + 5) _ (by omega)
  have f5 : coeff (k + 9) (C (2220360 : ℚ) * (X ^ 5 * OMA.A))
      = (2220360 : ℚ) * coeff (k + 4) OMA.A := OMA.cXf _ 5 _ (k + 4) _ (by omega)
  have z3 : coeff (k + 9) (C (200001 : ℚ) * X ^ 3 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 3 _ (by omega)
  have z4 : coeff (k + 9) (C (-1642287 : ℚ) * X ^ 4 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 4 _ (by omega)
  have z5 : coeff (k + 9) (C (4465368 : ℚ) * X ^ 5 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 5 _ (by omega)
  have z6 : coeff (k + 9) (C (-4015548 : ℚ) * X ^ 6 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 6 _ (by omega)
  have z7 : coeff (k + 9) (C (2145732 : ℚ) * X ^ 7 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 7 _ (by omega)
  have z8 : coeff (k + 9) (C (-1148064 : ℚ) * X ^ 8 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 8 _ (by omega)
  simp only [map_add, map_zero, s0, s1, s2, s3, s4, s5, t0, t1, t2, t3, t4, t5, f1, f2, f3, f4, f5, z3, z4, z5, z6, z7, z8] at hc
  have e0 : a (k + 7) = coeff (k + 9) OMA.A := by
    have h : k + 7 + 2 = k + 9 := by omega
    rw [OMA.a_eq, h]
  have e1 : a (k + 7 - 1) = coeff (k + 8) OMA.A := by
    have h : k + 7 - 1 + 2 = k + 8 := by omega
    rw [OMA.a_eq, h]
  have e2 : a (k + 7 - 2) = coeff (k + 7) OMA.A := by
    have h : k + 7 - 2 + 2 = k + 7 := by omega
    rw [OMA.a_eq, h]
  have e3 : a (k + 7 - 3) = coeff (k + 6) OMA.A := by
    have h : k + 7 - 3 + 2 = k + 6 := by omega
    rw [OMA.a_eq, h]
  have e4 : a (k + 7 - 4) = coeff (k + 5) OMA.A := by
    have h : k + 7 - 4 + 2 = k + 5 := by omega
    rw [OMA.a_eq, h]
  have e5 : a (k + 7 - 5) = coeff (k + 4) OMA.A := by
    have h : k + 7 - 5 + 2 = k + 4 := by omega
    rw [OMA.a_eq, h]
  rw [e0, e1, e2, e3, e4, e5]
  push_cast at hc ⊢
  linear_combination (1 / 1 : ℚ) * hc
