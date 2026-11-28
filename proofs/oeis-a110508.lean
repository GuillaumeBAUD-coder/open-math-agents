import OMAStatements.S_oeis_a110508

open PowerSeries

private noncomputable def euler (f : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  X * derivative ℚ f

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private theorem map_one_derivative : derivative ℚ (1 : ℚ⟦X⟧) = 0 :=
  derivative_one

private theorem coeff_euler (f : ℚ⟦X⟧) (n : ℕ) :
    coeff n (euler f) = (n : ℚ) * coeff n f := by
  cases n with
  | zero => simp [euler]
  | succ n =>
    rw [euler, coeff_succ_X_mul, coeff_derivative, mul_comm]
    simp

private theorem jet_step {b : ℚ} {q u f v : ℚ⟦X⟧} {k : ℕ}
    (h : C b * q ^ k * u = f)
    (hv : q * euler f - (k : ℚ⟦X⟧) * euler q * f = v) :
    C b * q ^ (k + 1) * euler u = v := by
  rw [← h] at hv
  simp only [euler, Derivation.leibniz, smul_eq_mul, derivative_C, derivative_pow,
    zero_mul, mul_zero, zero_add, add_zero] at hv
  unfold euler
  cases k with
  | zero => simpa [mul_assoc, mul_left_comm, mul_comm] using hv
  | succ k =>
    simp only [Nat.succ_sub_one, pow_succ] at hv ⊢
    linear_combination hv

set_option maxHeartbeats 300000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a110508.main := by
  intro T c G hInput _ hc hG n hn
  have hInv : G * (3 - X + (1 + X) * T) = 4 := by
    linear_combination 4 * hG + G * (1 + X) * hc
  have hT : (T ^ 2 + 8 * X - 1) = 0 := by linear_combination hInput
  let Q : ℚ⟦X⟧ := (-8 * X ^ 4 - 15 * X ^ 3 + 2 * X ^ 2 - 8 * X + 1)
  have hQ : Q ≠ 0 := by
    intro h
    have h0 := congrArg (constantCoeff (R := ℚ)) h
    norm_num [Q, map_pow, map_ofNat] at h0
  have hSlope := congrArg (fun f => derivative ℚ f) hInput
  simp only [euler, map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul,
      derivative_pow, derivative_X, derivative_numeral, map_one_derivative] at hSlope
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    simp
  have hSlopeHalf : T * derivative ℚ T = -4 := by
    apply mul_left_cancel₀ hTwo
    linear_combination hSlope
  have hTE : Q * euler T = (-4 * T * X ^ 4 - 8 * T * X ^ 3 - 4 * T * X) := by
    unfold Q euler
    linear_combination (T * X ^ 4 + 2 * T * X ^ 3 + T * X) * hSlopeHalf + ((-X ^ 4 * (derivative ℚ T) - 2 * X ^ 3 * (derivative ℚ T) - X * (derivative ℚ T))) * hT
  have hRational : (-T * X - T - X + 3) * (T * X + T - X + 3) = (8 * X ^ 3 + 16 * X ^ 2 + 8) := by
    linear_combination (-X ^ 2 - 2 * X - 1) * hT
  have hBase : C (2 : ℚ) * (X ^ 3 + 2 * X ^ 2 + 1) * G = (-T * X - T - X + 3) := by
    rw [map_ofNat C 2]
    apply mul_left_cancel₀ (mul_ne_zero hTwo hTwo)
    linear_combination (-T * X - T - X + 3) * hInv - G * hRational
  -- Clear the generating function denominator before differentiating.
  have h0 : C (2 : ℚ) * Q ^ 1 * G = (8 * T * X ^ 2 + 7 * T * X - T + 8 * X ^ 2 - 25 * X + 3) := by
    dsimp [Q]
    linear_combination (1 - 8 * X) * hBase
  have h1 : C (2 : ℚ) * Q ^ 2 * euler (G) = (96 * T * X ^ 6 + 196 * T * X ^ 5 + 126 * T * X ^ 4 - 147 * T * X ^ 3 - 8 * T * X ^ 2 + 3 * T * X + 128 * X ^ 6 - 480 * X ^ 5 - 654 * X ^ 4 + 121 * X ^ 3 + 4 * X ^ 2 - X) := by
    apply jet_step (k := 1) (f := (8 * T * X ^ 2 + 7 * T * X - T + 8 * X ^ 2 - 25 * X + 3)) (h0)
    unfold euler at hTE ⊢
    dsimp [Q] at hTE ⊢
    simp only [euler, map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul,
      derivative_pow, derivative_X, derivative_numeral, map_one_derivative]
    linear_combination (8 * X ^ 2 + 7 * X - 1) * hTE
  have h2 : C (2 : ℚ) * Q ^ 3 * euler (euler (G)) = (1152 * T * X ^ 10 + 3152 * T * X ^ 9 + 5284 * T * X ^ 8 - 5584 * T * X ^ 7 - 10703 * T * X ^ 6 - 1506 * T * X ^ 5 + 2501 * T * X ^ 4 - 427 * T * X ^ 3 - 4 * T * X ^ 2 + 3 * T * X + 2048 * X ^ 10 - 11520 * X ^ 9 - 27616 * X ^ 8 - 19836 * X ^ 7 + 17925 * X ^ 6 + 8006 * X ^ 5 - 3675 * X ^ 4 + 369 * X ^ 3 - X) := by
    apply jet_step (k := 2) (f := (96 * T * X ^ 6 + 196 * T * X ^ 5 + 126 * T * X ^ 4 - 147 * T * X ^ 3 - 8 * T * X ^ 2 + 3 * T * X + 128 * X ^ 6 - 480 * X ^ 5 - 654 * X ^ 4 + 121 * X ^ 3 + 4 * X ^ 2 - X)) (h1)
    unfold euler at hTE ⊢
    dsimp [Q] at hTE ⊢
    simp only [euler, map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul,
      derivative_pow, derivative_X, derivative_numeral, map_one_derivative]
    linear_combination (96 * X ^ 6 + 196 * X ^ 5 + 126 * X ^ 4 - 147 * X ^ 3 - 8 * X ^ 2 + 3 * X) * hTE
  -- Assemble the differential equation from the cleared derivatives.
  have hODE : X ^ 0 * (C (-7 : ℚ) * euler (G) + C (3 : ℚ) * euler (euler (G))) +
      X ^ 1 * (C (-12 : ℚ) * G + C (44 : ℚ) * euler (G) + C (-24 : ℚ) * euler (euler (G))) +
      X ^ 2 * (C (-4 : ℚ) * G + C (10 : ℚ) * euler (G) + C (6 : ℚ) * euler (euler (G))) +
      X ^ 3 * (C (-34 : ℚ) * G + C (-93 : ℚ) * euler (G) + C (-45 : ℚ) * euler (euler (G))) +
      X ^ 4 * (C (-96 : ℚ) * G + C (-100 : ℚ) * euler (G) + C (-24 : ℚ) * euler (euler (G))) = C (-4 : ℚ) * X ^ 2 + C (-16 : ℚ) * X ^ 1 := by
    apply mul_left_cancel₀ (a := C (2 : ℚ) * Q ^ 3)
      (mul_ne_zero (by simp) (pow_ne_zero _ hQ))
    simp only [map_one, map_ofNat, map_neg] at h0 h1 h2 ⊢
    dsimp [Q] at *
    linear_combination ((-96 * X ^ 4 - 34 * X ^ 3 - 4 * X ^ 2 - 12 * X) * (-8 * X ^ 4 - 15 * X ^ 3 + 2 * X ^ 2 - 8 * X + 1) ^ 2) * h0 + ((-100 * X ^ 4 - 93 * X ^ 3 + 10 * X ^ 2 + 44 * X - 7) * (-8 * X ^ 4 - 15 * X ^ 3 + 2 * X ^ 2 - 8 * X + 1) ^ 1) * h1 + ((-24 * X ^ 4 - 45 * X ^ 3 + 6 * X ^ 2 - 24 * X + 3) * (-8 * X ^ 4 - 15 * X ^ 3 + 2 * X ^ 2 - 8 * X + 1) ^ 0) * h2
  -- The polynomial on the right has no coefficient at the requested index.
  have hCoeff := congrArg (coeff n) hODE
  simp only [map_add, coeff_X_pow_mul',
    coeff_C_mul, coeff_euler, coeff_X_pow,
    Nat.sub_zero, if_pos (show 0 ≤ n by omega), if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega), if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 1 by omega), mul_zero, add_zero] at hCoeff
  simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega)] at hCoeff
  push_cast at hCoeff
  linear_combination hCoeff
