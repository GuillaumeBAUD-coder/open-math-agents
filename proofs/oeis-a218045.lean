import OMAStatements.S_oeis_a218045

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
theorem OMA.solution : type_of% @OMA.S_oeis_a218045.main := by
  intro T W G hInput _ hSquare hConst hG n hn
  have hW : (-2 * T + W ^ 2 - 8 * X - 2) = 0 := by linear_combination hSquare
  have hT : (T ^ 2 + 8 * X - 1) = 0 := by linear_combination hInput
  let Q : ℚ⟦X⟧ := (-32 * X ^ 2 - 28 * X + 4)
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
  have hTE : Q * euler T = (-16 * T * X ^ 2 - 16 * T * X) := by
    unfold Q euler
    linear_combination (4 * T * X ^ 2 + 4 * T * X) * hSlopeHalf + ((-4 * X ^ 2 * (derivative ℚ T) - 4 * X * (derivative ℚ T))) * hT
  have hWSlope := congrArg (fun f => derivative ℚ f) hSquare
  simp only [euler, map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul,
      derivative_pow, derivative_X, derivative_numeral, map_one_derivative] at hWSlope
  have hWSlopeHalf : W * derivative ℚ W = derivative ℚ T + 4 := by
    apply mul_left_cancel₀ hTwo
    linear_combination hWSlope
  have hWNe : W ≠ 0 := by
    intro h
    rw [h, map_zero] at hConst
    norm_num at hConst
  have hWE : Q * euler W = (2 * T * W * X - T * W - 16 * W * X ^ 2 - 6 * W * X + W) := by
    apply mul_left_cancel₀ hWNe
    unfold euler at hTE ⊢
    dsimp [Q] at hTE ⊢
    linear_combination (-32 * X ^ 3 - 28 * X ^ 2 + 4 * X) * hWSlopeHalf + (1) * hTE + (2 - 4 * X) * hT + (-2 * T * X + T + 16 * X ^ 2 + 6 * X - 1) * hW
  -- Clear the generating function denominator before differentiating.
  have h0 : C (8 : ℚ) * Q ^ 0 * G = (-T * W + 2 * T - W + 2) := by
    rw [map_ofNat C 8]
    simp only [pow_zero, mul_one]
    linear_combination hG
  have h1 : C (8 : ℚ) * Q ^ 1 * euler (G) = (32 * T * W * X ^ 2 + 20 * T * W * X - 32 * T * X ^ 2 - 32 * T * X + 32 * W * X ^ 2 - 4 * W * X) := by
    apply jet_step (k := 0) (f := (-T * W + 2 * T - W + 2)) (h0)
    unfold euler at hTE hWE ⊢
    dsimp [Q] at hTE hWE ⊢
    simp only [euler, map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul,
      derivative_pow, derivative_X, derivative_numeral, map_one_derivative]
    linear_combination (2 - W) * hTE + (-T - 1) * hWE + (-2 * W * X + W) * hT
  have h2 : C (8 : ℚ) * Q ^ 2 * euler (euler (G)) = (-1024 * T * W * X ^ 4 - 1536 * T * W * X ^ 3 - 192 * T * W * X ^ 2 + 104 * T * W * X + 512 * T * X ^ 4 + 896 * T * X ^ 3 + 256 * T * X ^ 2 - 128 * T * X - 1024 * W * X ^ 4 - 1152 * W * X ^ 3 + 480 * W * X ^ 2 - 40 * W * X) := by
    apply jet_step (k := 1) (f := (32 * T * W * X ^ 2 + 20 * T * W * X - 32 * T * X ^ 2 - 32 * T * X + 32 * W * X ^ 2 - 4 * W * X)) (h1)
    unfold euler at hTE hWE ⊢
    dsimp [Q] at hTE hWE ⊢
    simp only [euler, map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul,
      derivative_pow, derivative_X, derivative_numeral, map_one_derivative]
    linear_combination (32 * W * X ^ 2 + 20 * W * X - 32 * X ^ 2 - 32 * X) * hTE + (32 * T * X ^ 2 + 20 * T * X + 32 * X ^ 2 - 4 * X) * hWE + (64 * W * X ^ 3 + 8 * W * X ^ 2 - 20 * W * X) * hT
  have h3 : C (8 : ℚ) * Q ^ 3 * euler (euler (euler (G))) = (32768 * T * W * X ^ 6 + 77824 * T * W * X ^ 5 + 51968 * T * W * X ^ 4 - 6976 * T * W * X ^ 3 - 1664 * T * W * X ^ 2 + 560 * T * W * X - 8192 * T * X ^ 6 - 22528 * T * X ^ 5 - 18944 * T * X ^ 4 - 3584 * T * X ^ 3 + 512 * T * X ^ 2 - 512 * T * X + 32768 * W * X ^ 6 + 59392 * W * X ^ 5 + 33536 * W * X ^ 4 - 23104 * W * X ^ 3 + 4672 * W * X ^ 2 - 304 * W * X) := by
    apply jet_step (k := 2) (f := (-1024 * T * W * X ^ 4 - 1536 * T * W * X ^ 3 - 192 * T * W * X ^ 2 + 104 * T * W * X + 512 * T * X ^ 4 + 896 * T * X ^ 3 + 256 * T * X ^ 2 - 128 * T * X - 1024 * W * X ^ 4 - 1152 * W * X ^ 3 + 480 * W * X ^ 2 - 40 * W * X)) (h2)
    unfold euler at hTE hWE ⊢
    dsimp [Q] at hTE hWE ⊢
    simp only [euler, map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul,
      derivative_pow, derivative_X, derivative_numeral, map_one_derivative]
    linear_combination (-1024 * W * X ^ 4 - 1536 * W * X ^ 3 - 192 * W * X ^ 2 + 104 * W * X + 512 * X ^ 4 + 896 * X ^ 3 + 256 * X ^ 2 - 128 * X) * hTE + (-1024 * T * X ^ 4 - 1536 * T * X ^ 3 - 192 * T * X ^ 2 + 104 * T * X - 1024 * X ^ 4 - 1152 * X ^ 3 + 480 * X ^ 2 - 40 * X) * hWE + (-2048 * W * X ^ 5 - 2048 * W * X ^ 4 + 1152 * W * X ^ 3 + 400 * W * X ^ 2 - 104 * W * X) * hT
  -- Assemble the differential equation from the cleared derivatives.
  have hODE : X ^ 0 * (C (3 : ℚ) * euler (G) + C (-5 : ℚ) * euler (euler (G)) + C (2 : ℚ) * euler (euler (euler (G)))) +
      X ^ 1 * (C (-14 : ℚ) * euler (G) + C (34 : ℚ) * euler (euler (G)) + C (-22 : ℚ) * euler (euler (euler (G)))) +
      X ^ 2 * (C (8 : ℚ) * G + C (-216 : ℚ) * euler (G) + C (192 : ℚ) * euler (euler (G)) + C (-24 : ℚ) * euler (euler (euler (G)))) +
      X ^ 3 * (C (-128 : ℚ) * G + C (672 : ℚ) * euler (G) + C (-1088 : ℚ) * euler (euler (G)) + C (512 : ℚ) * euler (euler (euler (G)))) +
      X ^ 4 * (C (128 : ℚ) * G + C (-128 : ℚ) * euler (G) + C (-512 : ℚ) * euler (euler (G)) + C (512 : ℚ) * euler (euler (euler (G)))) = C (32 : ℚ) * X ^ 4 + C (-32 : ℚ) * X ^ 3 + C (2 : ℚ) * X ^ 2 := by
    apply mul_left_cancel₀ (a := C (8 : ℚ) * Q ^ 3)
      (mul_ne_zero (by simp) (pow_ne_zero _ hQ))
    simp only [map_one, map_ofNat, map_neg] at h0 h1 h2 h3 ⊢
    dsimp [Q] at *
    linear_combination ((128 * X ^ 4 - 128 * X ^ 3 + 8 * X ^ 2) * (-32 * X ^ 2 - 28 * X + 4) ^ 3) * h0 + ((-128 * X ^ 4 + 672 * X ^ 3 - 216 * X ^ 2 - 14 * X + 3) * (-32 * X ^ 2 - 28 * X + 4) ^ 2) * h1 + ((-512 * X ^ 4 - 1088 * X ^ 3 + 192 * X ^ 2 + 34 * X - 5) * (-32 * X ^ 2 - 28 * X + 4) ^ 1) * h2 + ((512 * X ^ 4 + 512 * X ^ 3 - 24 * X ^ 2 - 22 * X + 2) * (-32 * X ^ 2 - 28 * X + 4) ^ 0) * h3
  -- The polynomial on the right has no coefficient at the requested index.
  have hCoeff := congrArg (coeff n) hODE
  simp only [map_add, coeff_X_pow_mul',
    coeff_C_mul, coeff_euler, coeff_X_pow,
    Nat.sub_zero, if_pos (show 0 ≤ n by omega), if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega), if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 2 by omega), mul_zero, add_zero] at hCoeff
  simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega)] at hCoeff
  push_cast at hCoeff
  linear_combination hCoeff
