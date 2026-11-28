import OMAStatements.S_oeis_a116388

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

private theorem generating_function_ode (S M G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hM : 2 * X ^ 2 * M = 1 - X - S)
    (hG : G * ((1 + X * (1 - M)) * S) = 1) :
    X * derivative ℚ G - C 7 * (X * (X * derivative ℚ G)) +
      C 8 * (X ^ 2 * (X * derivative ℚ G)) - C 2 * (X ^ 2 * G) +
      C 25 * (X ^ 3 * (X * derivative ℚ G)) + C 17 * (X ^ 3 * G) -
      C 18 * (X ^ 4 * (X * derivative ℚ G)) - C 7 * (X ^ 4 * G) -
      C 52 * (X ^ 5 * (X * derivative ℚ G)) - C 61 * (X ^ 5 * G) -
      C 31 * (X ^ 6 * (X * derivative ℚ G)) - C 51 * (X ^ 6 * G) -
      C 6 * (X ^ 7 * (X * derivative ℚ G)) - C 12 * (X ^ 7 * G) =
      X - X ^ 2 - C 3 * X ^ 3 - C 3 * X ^ 4 := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    intro h
    have h0 := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at h0
    norm_num at h0
  have hTwoX : (2 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h1 := congrArg (coeff 1) h
    rw [map_zero, ← map_ofNat C 2, coeff_C_mul, coeff_X] at h1
    norm_num at h1
  let A : ℚ⟦X⟧ := 1 - 2 * X - 3 * X ^ 2
  let B : ℚ⟦X⟧ := -1 + 3 * X + 2 * X ^ 2
  let Q : ℚ⟦X⟧ := 1 - 2 * X - 3 * X ^ 2 - X ^ 3
  have hA_ne : A ≠ 0 := by
    intro h
    have h0 := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    dsimp only [A] at h0
    simp at h0
  have hQG : 2 * A * Q * G = A - B * S := by
    apply mul_left_cancel₀ hTwoX
    dsimp only [A, B, Q]
    linear_combination
      2 * X * (A - B * S) * hG +
      S * (A - B * S) * G * hM +
      (-(A - B * S) + B ^ 2) * G * hSq
  have hSqDerivative : 2 * S * derivative ℚ S = -2 - 6 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp only [pow_succ, pow_zero, derivative_numeral, Derivation.leibniz, map_sub,
      derivative_one, derivative_X, smul_eq_mul, zero_mul, add_zero, sub_zero, one_mul] at hd
    linear_combination hd
  have hRadicalODE : 2 * A * derivative ℚ S = (-2 - 6 * X) * S := by
    dsimp only [A]
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  have hQGDeriv :
      2 * ((-2 - 6 * X) * Q + A * (-2 - 6 * X - 3 * X ^ 2)) * G +
        2 * A * Q * derivative ℚ G =
      (-2 - 6 * X) - (3 + 4 * X) * S - B * derivative ℚ S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hQG
    dsimp only [A, B, Q] at hd
    simp only [pow_succ, pow_zero, derivative_numeral, Derivation.leibniz, map_sub, map_add,
      map_neg, derivative_one, derivative_X, smul_eq_mul, neg_zero, mul_one, one_mul] at hd
    dsimp only [A, B, Q]
    linear_combination hd
  have hElim :
      2 * A * B * (2 * ((-2 - 6 * X) * Q + A * (-2 - 6 * X - 3 * X ^ 2)) * G +
        2 * A * Q * derivative ℚ G) =
      2 * A * (-2 - 6 * X) * B -
        (2 * A * (3 + 4 * X) + (-2 - 6 * X) * B) * (A - 2 * A * Q * G) := by
    linear_combination
      2 * A * B * hQGDeriv -
      (2 * A * (3 + 4 * X) + (-2 - 6 * X) * B) * hQG -
      B ^ 2 * hRadicalODE
  have hCancelA :
      2 * B * (2 * ((-2 - 6 * X) * Q + A * (-2 - 6 * X - 3 * X ^ 2)) * G +
        2 * A * Q * derivative ℚ G) =
      2 * (-2 - 6 * X) * B -
        (2 * A * (3 + 4 * X) + (-2 - 6 * X) * B) * (1 - 2 * Q * G) := by
    apply mul_left_cancel₀ hA_ne
    linear_combination hElim
  have hFour : (4 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 4]
    intro h
    have h0 := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (4 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at h0
    norm_num at h0
  rw [map_ofNat C 7, map_ofNat C 8, map_ofNat C 2, map_ofNat C 25, map_ofNat C 17,
    map_ofNat C 18, map_ofNat C 52, map_ofNat C 61, map_ofNat C 31, map_ofNat C 51,
    map_ofNat C 6, map_ofNat C 12, map_ofNat C 3]
  apply mul_left_cancel₀ hFour
  dsimp only [A, B, Q] at hCancelA
  linear_combination -X * hCancelA

theorem OMA.solution : type_of% @OMA.S_oeis_a116388.main := by
  intro S M G hSq _ hM hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have hcoeff := congrArg (coeff (m + 7)) (generating_function_ode S M G hSq hM hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_X, coeff_X_pow] at hcoeff
  rw [coeff_X_derivative,
    coeff_X_mul_X_derivative G (by omega),
    coeff_X_pow_mul_X_derivative G 2 (by omega), coeff_X_pow_mul_le 2 (by omega),
    coeff_X_pow_mul_X_derivative G 3 (by omega), coeff_X_pow_mul_le 3 (by omega),
    coeff_X_pow_mul_X_derivative G 4 (by omega), coeff_X_pow_mul_le 4 (by omega),
    coeff_X_pow_mul_X_derivative G 5 (by omega), coeff_X_pow_mul_le 5 (by omega),
    coeff_X_pow_mul_X_derivative G 6 (by omega), coeff_X_pow_mul_le 6 (by omega),
    coeff_X_pow_mul_X_derivative G 7 (by omega), coeff_X_pow_mul_le 7 (by omega)] at hcoeff
  simp only [eq_false (by omega : m + 7 ≠ 1),
    eq_false (by omega : m + 7 ≠ 2),
    eq_false (by omega : m + 7 ≠ 3),
    eq_false (by omega : m + 7 ≠ 4), if_false,
    show m + 7 - 1 = m + 6 by omega,
    show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega,
    show m + 7 - 4 = m + 3 by omega,
    show m + 7 - 5 = m + 2 by omega,
    show m + 7 - 6 = m + 1 by omega,
    show m + 7 - 7 = m by omega] at hcoeff ⊢
  push_cast at hcoeff ⊢
  linear_combination hcoeff
