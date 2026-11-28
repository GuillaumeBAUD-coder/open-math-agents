import OMAStatements.S_oeis_a155051

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

theorem OMA.solution : type_of% @OMA.S_oeis_a155051.main := by
  intro S G hS _ hG n hn
  have twoNeZero : (2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff (R := ℚ)) h
    norm_num [map_ofNat] at hc
  have dTwo : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := (d⁄dX ℚ).map_natCast 2
  have dFour : d⁄dX ℚ (4 : ℚ⟦X⟧) = 0 := (d⁄dX ℚ).map_natCast 4
  let P : ℚ⟦X⟧ := 1 - 4 * X ^ 2

  -- The squared relation gives two linear identities for the derivatives of S.
  have hSd : S * d⁄dX ℚ S = -4 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) hS
    change d⁄dX ℚ (S ^ 2) = d⁄dX ℚ (1 - 4 * X ^ 2) at hd
    simp only [derivative_pow, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz,
      smul_eq_mul, derivative_X, dFour] at hd
    apply mul_left_cancel₀ twoNeZero
    linear_combination hd
  have hP1 : P * d⁄dX ℚ S = -4 * X * S := by
    dsimp [P]
    linear_combination S * hSd - d⁄dX ℚ S * hS
  have hP2 : P * d⁄dX ℚ (d⁄dX ℚ S) = 4 * X * d⁄dX ℚ S - 4 * S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) hP1
    change d⁄dX ℚ (P * d⁄dX ℚ S) = d⁄dX ℚ (-4 * X * S) at hd
    have dP : d⁄dX ℚ P = -8 * X := by
      simp only [P, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz,
        smul_eq_mul, dFour, derivative_pow, derivative_X]
      ring
    simp only [Derivation.leibniz, smul_eq_mul, dP, map_neg, dFour, derivative_X] at hd
    linear_combination hd

  -- Transfer the equation through 2 X² F = (1 + X)(1 - S).
  let F : ℚ⟦X⟧ := (1 - X) * G
  have hF : 2 * X ^ 2 * F = (1 + X) * (1 - S) := by
    simpa only [F, mul_assoc] using hG
  have hF1 : 4 * X * F + 2 * X ^ 2 * d⁄dX ℚ F = 1 - S - (1 + X) * d⁄dX ℚ S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) hF
    change d⁄dX ℚ (2 * X ^ 2 * F) = d⁄dX ℚ ((1 + X) * (1 - S)) at hd
    simp only [Derivation.leibniz, smul_eq_mul, dTwo, derivative_pow, derivative_X,
      map_add, map_sub, Derivation.map_one_eq_zero] at hd
    linear_combination hd
  have hF2 : 4 * F + 8 * X * d⁄dX ℚ F + 2 * X ^ 2 * d⁄dX ℚ (d⁄dX ℚ F) =
      -2 * d⁄dX ℚ S - (1 + X) * d⁄dX ℚ (d⁄dX ℚ S) := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) hF1
    change d⁄dX ℚ (4 * X * F + 2 * X ^ 2 * d⁄dX ℚ F) =
      d⁄dX ℚ (1 - S - (1 + X) * d⁄dX ℚ S) at hd
    simp only [Derivation.leibniz, smul_eq_mul, dTwo, dFour, derivative_pow, derivative_X,
      map_add, map_sub, Derivation.map_one_eq_zero] at hd
    linear_combination hd
  have odeF : -(X ^ 2 * P) * d⁄dX ℚ (d⁄dX ℚ F) + 4 * X ^ 3 * d⁄dX ℚ F + (6 - 4 * X) * F =
      6 + 2 * X := by
    apply mul_left_cancel₀ twoNeZero
    apply X_pow_mul_cancel (k := 2)
    dsimp only [P] at hP1 hP2 ⊢
    linear_combination
      -(X ^ 2 * (1 - 4 * X ^ 2)) * hF2 + (4 * X - 12 * X ^ 3) * hF1 +
      (16 * X ^ 2 - 4 * X) * hF + X ^ 2 * (1 + X) * hP2 -
      (4 * X + 2 * X ^ 2) * hP1

  -- The Euler derivative weights the nth coefficient by n.
  have odeG :
      6 * G + euler G - euler (euler G) +
        X ^ 1 * (-10 * G + euler G + euler (euler G)) +
        X ^ 2 * (4 * G + 4 * euler (euler G)) +
        X ^ 3 * (-4 * G - 8 * euler G - 4 * euler (euler G)) = 6 + 2 * X := by
    dsimp only [F, P] at odeF
    simp only [euler, Derivation.leibniz, smul_eq_mul, map_add, map_sub,
      Derivation.map_one_eq_zero, derivative_X, map_zero] at odeF ⊢
    linear_combination odeF

  have hc := congrArg (coeff n) odeG
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have shift1 := coeff_shift n 1 (by omega)
  have shift2 := coeff_shift n 2 (by omega)
  have shift3 := coeff_shift n 3 hn
  simp only [map_add, map_sub, shift1, shift2, shift3, map_neg, neg_mul, ← map_ofNat C,
    coeff_C_mul, coeff_euler, coeff_C, coeff_X, if_neg hn0, if_neg hn1, mul_zero, add_zero] at hc
  have cast1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have cast2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat]
  have cast3 : ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 := by
    rw [Nat.cast_sub hn, Nat.cast_ofNat]
  rw [cast1, cast2, cast3] at hc
  linear_combination hc
