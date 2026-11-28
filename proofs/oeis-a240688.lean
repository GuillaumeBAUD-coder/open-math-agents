import OMAStatements.S_oeis_a240688

open PowerSeries

private noncomputable def euler (f : ℚ⟦X⟧) : ℚ⟦X⟧ := X * d⁄dX ℚ f

private theorem coeff_euler (n : ℕ) (f : ℚ⟦X⟧) :
    coeff n (euler f) = coeff n f * (n : ℚ) := by
  cases n with
  | zero => simp [euler, coeff_zero_X_mul]
  | succ n => simp [euler, coeff_derivative, Nat.cast_succ]

private theorem coeff_shift (n k : ℕ) (h : k ≤ n) (f : ℚ⟦X⟧) :
    coeff n (X ^ k * f) = coeff (n - k) f := by
  conv_lhs => rw [← Nat.sub_add_cancel h]
  exact coeff_X_pow_mul f k (n - k)

private theorem ne_zero_of_const_one (f : ℚ⟦X⟧) (h : constantCoeff f = 1) : f ≠ 0 := by
  intro hf
  rw [hf, map_zero] at h
  exact zero_ne_one h

theorem OMA.solution : type_of% @OMA.S_oeis_a240688.main := by
  intro S G hS h0 hG n hn
  have twoNeZero : (2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff (R := ℚ)) h
    norm_num [map_ofNat] at hc
  have dTwo : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := (d⁄dX ℚ).map_natCast 2
  have dFour : d⁄dX ℚ (4 : ℚ⟦X⟧) = 0 := (d⁄dX ℚ).map_natCast 4
  have dSix : d⁄dX ℚ (6 : ℚ⟦X⟧) = 0 := (d⁄dX ℚ).map_natCast 6
  have hSne : S ≠ 0 := by
    apply ne_zero_of_const_one
    rwa [← coeff_zero_eq_constantCoeff_apply]
  have hX1 : (X + 1 : ℚ⟦X⟧) ≠ 0 := ne_zero_of_const_one _ (by simp)
  have h2X : (1 + 2 * X : ℚ⟦X⟧) ≠ 0 := ne_zero_of_const_one _ (by simp)

  -- Rationalise the defining relation.
  have key : S * (2 * (X + 1) * G - 1) = 1 + 2 * X := by
    have h : 2 * (X + 1) * S * G - S - 2 * X - 1 = 0 := by
      have hfac : (2 * X * (X + 1) ^ 2 * S : ℚ⟦X⟧) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero twoNeZero X_ne_zero) (pow_ne_zero 2 hX1)) hSne
      apply mul_left_cancel₀ hfac
      linear_combination ((X + 1) * S - (4 * X ^ 3 + 8 * X ^ 2 + 3 * X - 1)) * hG +
        (G * (4 * X * (X + 1) ^ 3 - (X + 1) ^ 2) - 2 * X * (X + 1) ^ 2 - X * (X + 1)) * hS
    linear_combination h

  let F : ℚ⟦X⟧ := 2 * (X + 1) * G - 1
  have hF : S * F = 1 + 2 * X := key
  have hSd : S * d⁄dX ℚ S = -2 - 4 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) hS
    change d⁄dX ℚ (S ^ 2) = d⁄dX ℚ (1 - 4 * X - 4 * X ^ 2) at hd
    simp only [derivative_pow, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz,
      smul_eq_mul, derivative_X, dFour] at hd
    push_cast at hd
    apply mul_left_cancel₀ twoNeZero
    linear_combination hd
  have hFd : S * d⁄dX ℚ F + F * d⁄dX ℚ S = 2 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) hF
    change d⁄dX ℚ (S * F) = d⁄dX ℚ (1 + 2 * X) at hd
    simp only [map_add, Derivation.map_one_eq_zero, Derivation.leibniz,
      smul_eq_mul, derivative_X, dTwo] at hd
    linear_combination hd
  have h4 : S * d⁄dX ℚ F * (1 - 4 * X - 4 * X ^ 2) = 4 := by
    linear_combination (1 - 4 * X - 4 * X ^ 2) * hFd +
      d⁄dX ℚ S * F * hS - (S * F) * hSd - (-2 - 4 * X) * hF
  have ode1 : (1 + 2 * X) * (1 - 4 * X - 4 * X ^ 2) * d⁄dX ℚ F = 4 * F := by
    linear_combination F * h4 - (1 - 4 * X - 4 * X ^ 2) * d⁄dX ℚ F * hF
  have ode2 : (1 - 4 * X - 4 * X ^ 2) * d⁄dX ℚ (d⁄dX ℚ F) -
      6 * (1 + 2 * X) * d⁄dX ℚ F = 0 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) ode1
    change d⁄dX ℚ ((1 + 2 * X) * (1 - 4 * X - 4 * X ^ 2) * d⁄dX ℚ F) = d⁄dX ℚ (4 * F) at hd
    simp only [derivative_pow, map_add, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz,
      smul_eq_mul, derivative_X, dTwo, dFour] at hd
    push_cast at hd
    apply mul_left_cancel₀ h2X
    linear_combination hd

  have hF1 : d⁄dX ℚ F = 2 * G + 2 * (X + 1) * d⁄dX ℚ G := by
    simp only [F, map_add, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz,
      smul_eq_mul, derivative_X, dTwo]
    ring
  have hF2 : d⁄dX ℚ (d⁄dX ℚ F) = 4 * d⁄dX ℚ G + 2 * (X + 1) * d⁄dX ℚ (d⁄dX ℚ G) := by
    rw [hF1]
    simp only [map_add, Derivation.map_one_eq_zero, Derivation.leibniz,
      smul_eq_mul, derivative_X, dTwo]
    ring
  have odeD : (X + 1) * (1 - 4 * X - 4 * X ^ 2) * d⁄dX ℚ (d⁄dX ℚ G) -
      (4 + 26 * X + 20 * X ^ 2) * d⁄dX ℚ G - (6 + 12 * X) * G = 0 := by
    rw [hF2, hF1] at ode2
    apply mul_left_cancel₀ twoNeZero
    linear_combination ode2

  have odeG :
      euler (euler G) - euler G + X ^ 1 * (-3 * euler (euler G) - euler G) +
        X ^ 2 * (-8 * euler (euler G) - 18 * euler G - 6 * G) +
        X ^ 3 * (-4 * euler (euler G) - 16 * euler G - 12 * G) = 0 := by
    simp only [euler, Derivation.leibniz, smul_eq_mul, derivative_X]
    linear_combination X ^ 2 * odeD

  have hc := congrArg (coeff n) odeG
  have shift1 := coeff_shift n 1 (by omega)
  have shift2 := coeff_shift n 2 (by omega)
  have shift3 := coeff_shift n 3 hn
  simp only [map_add, map_sub, shift1, shift2, shift3, map_neg, neg_mul,
    ← map_ofNat C, coeff_C_mul, coeff_euler, map_zero] at hc
  have cast1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have cast2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat]
  have cast3 : ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 := by
    rw [Nat.cast_sub hn, Nat.cast_ofNat]
  rw [cast1, cast2, cast3] at hc
  linear_combination hc
