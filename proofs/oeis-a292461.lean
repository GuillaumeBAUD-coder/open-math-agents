import OMAStatements.S_oeis_a292461

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

theorem OMA.solution : type_of% @OMA.S_oeis_a292461.main := by
  intro S G hS _ hG n hn
  have twoNeZero : (2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff (R := ℚ)) h
    norm_num [map_ofNat] at hc
  have dTwo : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := (d⁄dX ℚ).map_natCast 2
  have dFour : d⁄dX ℚ (4 : ℚ⟦X⟧) = 0 := (d⁄dX ℚ).map_natCast 4

  have hSd : 2 * S * d⁄dX ℚ S = -2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) hS
    change d⁄dX ℚ (S ^ 2) = d⁄dX ℚ ((1 - X - X ^ 2) ^ 2 - 4 * X ^ 3) at hd
    simp only [derivative_pow, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz,
      smul_eq_mul, derivative_X, dFour] at hd
    push_cast at hd
    linear_combination hd
  have hQS : ((1 - X - X ^ 2) ^ 2 - 4 * X ^ 3) * d⁄dX ℚ S =
      (-1 - X - 3 * X ^ 2 + 2 * X ^ 3) * S := by
    apply mul_left_cancel₀ twoNeZero
    linear_combination S * hSd - 2 * d⁄dX ℚ S * hS
  have hGd : 2 * d⁄dX ℚ G = -1 - 2 * X + d⁄dX ℚ S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) hG
    change d⁄dX ℚ (2 * G) = d⁄dX ℚ (1 - X - X ^ 2 + S) at hd
    simp only [derivative_pow, map_add, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz,
      smul_eq_mul, derivative_X, dTwo] at hd
    push_cast at hd
    linear_combination hd

  have ode : ((1 - X - X ^ 2) ^ 2 - 4 * X ^ 3) * (X * d⁄dX ℚ G) -
      X * (-1 - X - 3 * X ^ 2 + 2 * X ^ 3) * G = 3 * X ^ 3 - X ^ 4 + X ^ 5 := by
    apply mul_left_cancel₀ twoNeZero
    linear_combination X * ((1 - X - X ^ 2) ^ 2 - 4 * X ^ 3) * hGd -
      X * (-1 - X - 3 * X ^ 2 + 2 * X ^ 3) * hG + X * hQS

  have odeG :
      euler G + X ^ 1 * (-2 * euler G + G) + X ^ 2 * (-1 * euler G + G) +
        X ^ 3 * (-2 * euler G + 3 * G) + X ^ 4 * (euler G - 2 * G) =
      3 * X ^ 3 - X ^ 4 + X ^ 5 := by
    simp only [euler]
    linear_combination ode

  have hc := congrArg (coeff n) odeG
  have shift1 := coeff_shift n 1 (by omega)
  have shift2 := coeff_shift n 2 (by omega)
  have shift3 := coeff_shift n 3 (by omega)
  have shift4 := coeff_shift n 4 (by omega)
  have hn3 : n ≠ 3 := by omega
  have hn4 : n ≠ 4 := by omega
  have hn5 : n ≠ 5 := by omega
  simp only [map_add, map_sub, shift1, shift2, shift3, shift4, map_neg, neg_mul, one_mul,
    ← map_ofNat C, coeff_C_mul, coeff_euler, coeff_X_pow, if_neg hn3, if_neg hn4, if_neg hn5,
    mul_zero, add_zero, sub_zero] at hc
  have cast1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have cast2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat]
  have cast3 : ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_ofNat]
  have cast4 : ((n - 4 : ℕ) : ℚ) = (n : ℚ) - 4 := by
    rw [Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_ofNat]
  rw [cast1, cast2, cast3, cast4] at hc
  linear_combination hc
