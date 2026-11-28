import OMAStatements.S_oeis_a135582

open PowerSeries

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private theorem coeff_X_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff k (X * derivative ℚ G) = (k : ℚ) * coeff k G := by
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative, mul_comm]
    simp only [Nat.cast_add, Nat.cast_one]

private theorem coeff_X_pow_mul_le (d : ℕ) {k : ℕ} (h : d ≤ k) (f : ℚ⟦X⟧) :
    coeff k (X ^ d * f) = coeff (k - d) f := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [Nat.add_sub_cancel, coeff_X_pow_mul]

private theorem coeff_X_mul_le {k : ℕ} (h : 1 ≤ k) (f : ℚ⟦X⟧) :
    coeff k (X * f) = coeff (k - 1) f := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [Nat.add_sub_cancel, coeff_succ_X_mul]

private theorem coeff_X_mul_X_derivative (G : ℚ⟦X⟧) {k : ℕ} (h : 1 ≤ k) :
    coeff k (X * (X * derivative ℚ G)) = ((k - 1 : ℕ) : ℚ) * coeff (k - 1) G := by
  rw [coeff_X_mul_le h, coeff_X_derivative]

private theorem coeff_X_pow_mul_X_derivative (G : ℚ⟦X⟧) (d : ℕ) {k : ℕ} (h : d ≤ k) :
    coeff k (X ^ d * (X * derivative ℚ G)) = ((k - d : ℕ) : ℚ) * coeff (k - d) G := by
  rw [coeff_X_pow_mul_le d h, coeff_X_derivative]

private theorem generating_function_ode (S c G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X)
    (hc : 2 * X * c = 1 - S)
    (hG : G * ((1 - X ^ 2 * c) * (1 - X - 2 * X ^ 2)) = 1) :
    G - X * derivative ℚ G - C 6 * (X * G) + C 6 * (X * (X * derivative ℚ G)) +
      C 5 * (X ^ 2 * G) - C 7 * (X ^ 2 * (X * derivative ℚ G)) - C 8 * (X ^ 3 * G) -
      C 7 * (X ^ 3 * (X * derivative ℚ G)) + C 21 * (X ^ 4 * G) +
      C 13 * (X ^ 4 * (X * derivative ℚ G)) - C 2 * (X ^ 5 * G) -
      C 2 * (X ^ 5 * (X * derivative ℚ G)) - C 28 * (X ^ 6 * G) -
      C 8 * (X ^ 6 * (X * derivative ℚ G)) = 1 - C 6 * X + X ^ 2 := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    intro h
    have h0 := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at h0
    norm_num at h0
  set P : ℚ⟦X⟧ := 2 * (1 - X + X ^ 3) * (1 - X - 2 * X ^ 2)
  have hPG : P * G = 2 - X - X * S := by
    apply mul_left_cancel₀ hTwo
    dsimp only [P]
    linear_combination
      2 * (2 - X - X * S) * hG +
      (1 - X - 2 * X ^ 2) * (2 - X - X * S) * G * X * hc +
      X ^ 2 * (1 - X - 2 * X ^ 2) * G * hSq
  have hSqDerivative : 2 * S * derivative ℚ S = -4 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadicalODE : (1 - 4 * X) * derivative ℚ S = -2 * S := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  have hPGDeriv :
      (-4 - 4 * X + 18 * X ^ 2 - 8 * X ^ 3 - 20 * X ^ 4) * G + P * derivative ℚ G =
        -1 - S - X * derivative ℚ S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hPG
    dsimp only [P] at hd
    simp only [pow_succ, pow_zero, derivative_numeral, Derivation.leibniz, map_sub, map_add,
      derivative_one, derivative_X, smul_eq_mul, zero_sub, mul_one, one_mul] at hd
    dsimp only [P]
    linear_combination hd
  have hODE2 :
      X * (1 - 4 * X) * ((-4 - 4 * X + 18 * X ^ 2 - 8 * X ^ 3 - 20 * X ^ 4) * G +
        P * derivative ℚ G + 1) + (1 - 6 * X) * (2 - X - P * G) = 0 := by
    linear_combination
      X * (1 - 4 * X) * hPGDeriv - (1 - 6 * X) * hPG - X ^ 2 * hRadicalODE
  rw [map_ofNat C 6, map_ofNat C 5, map_ofNat C 7, map_ofNat C 8, map_ofNat C 21,
    map_ofNat C 13, map_ofNat C 2, map_ofNat C 28]
  apply mul_left_cancel₀ hTwo
  dsimp only [P] at hODE2
  linear_combination -hODE2

theorem OMA.solution : type_of% @OMA.S_oeis_a135582.main := by
  intro S c G hSq _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have hcoeff := congrArg (coeff (m + 6)) (generating_function_ode S c G hSq hc hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_one, coeff_X, coeff_X_pow] at hcoeff
  rw [coeff_X_derivative, coeff_X_mul_le (by omega),
    coeff_X_mul_X_derivative G (by omega),
    coeff_X_pow_mul_le 2 (by omega), coeff_X_pow_mul_X_derivative G 2 (by omega),
    coeff_X_pow_mul_le 3 (by omega), coeff_X_pow_mul_X_derivative G 3 (by omega),
    coeff_X_pow_mul_le 4 (by omega), coeff_X_pow_mul_X_derivative G 4 (by omega),
    coeff_X_pow_mul_le 5 (by omega), coeff_X_pow_mul_X_derivative G 5 (by omega),
    coeff_X_pow_mul_le 6 (by omega), coeff_X_pow_mul_X_derivative G 6 (by omega)] at hcoeff
  simp only [eq_false (by omega : m + 6 ≠ 0), eq_false (by omega : m + 6 ≠ 1),
    eq_false (by omega : m + 6 ≠ 2), if_false,
    show m + 6 - 1 = m + 5 by omega,
    show m + 6 - 2 = m + 4 by omega,
    show m + 6 - 3 = m + 3 by omega,
    show m + 6 - 4 = m + 2 by omega,
    show m + 6 - 5 = m + 1 by omega,
    show m + 6 - 6 = m by omega] at hcoeff ⊢
  push_cast at hcoeff ⊢
  linear_combination hcoeff
