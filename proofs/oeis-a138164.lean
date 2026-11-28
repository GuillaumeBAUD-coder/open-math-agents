import OMAStatements.S_oeis_a138164

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
theorem OMA.solution : type_of% @OMA.S_oeis_a138164.main := by
  intro T G hInput _ hG n hn
  have hT : (T ^ 3 - T + X) = 0 := by linear_combination -hInput
  let Q : ℚ⟦X⟧ := (27 * X ^ 4 - 81 * X ^ 3 + 23 * X ^ 2 + 12 * X - 4)
  have hQ : Q ≠ 0 := by
    intro h
    have h0 := congrArg (constantCoeff (R := ℚ)) h
    norm_num [Q, map_pow, map_ofNat] at h0
  have hSlope := congrArg (fun f => derivative ℚ f) hInput
  simp only [euler, map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul,
      derivative_pow, derivative_X, derivative_numeral, map_one_derivative] at hSlope
  have hTE : Q * euler T = (6 * T ^ 2 * X ^ 3 - 18 * T ^ 2 * X ^ 2 + 6 * T ^ 2 * X + 9 * T * X ^ 4 - 27 * T * X ^ 3 + 9 * T * X ^ 2 - 4 * X ^ 3 + 12 * X ^ 2 - 4 * X) := by
    unfold Q euler
    linear_combination (6 * T ^ 2 * X ^ 3 - 18 * T ^ 2 * X ^ 2 + 6 * T ^ 2 * X + 9 * T * X ^ 4 - 27 * T * X ^ 3 + 9 * T * X ^ 2 - 4 * X ^ 3 + 12 * X ^ 2 - 4 * X) * hSlope + ((18 * T * X ^ 3 * (derivative ℚ T) - 54 * T * X ^ 2 * (derivative ℚ T) + 18 * T * X * (derivative ℚ T) + 27 * X ^ 4 * (derivative ℚ T) - 81 * X ^ 3 * (derivative ℚ T) + 27 * X ^ 2 * (derivative ℚ T))) * hT
  have hRational : (-T ^ 2 + T * X - T - X + 1) * (-T ^ 2 - T + 1) = (X ^ 2 - 3 * X + 1) := by
    linear_combination (T - X + 2) * hT
  have hBase : C (1 : ℚ) * (X ^ 2 - 3 * X + 1) * G = (-T ^ 2 + T * X - T - X + 1) := by
    simp only [map_one]
    linear_combination (-T ^ 2 + T * X - T - X + 1) * hG - G * hRational
  -- Clear the generating function denominator before differentiating.
  have h0 : C (1 : ℚ) * Q ^ 1 * G = (-27 * T ^ 2 * X ^ 2 + 4 * T ^ 2 + 27 * T * X ^ 3 - 27 * T * X ^ 2 - 4 * T * X + 4 * T - 27 * X ^ 3 + 27 * X ^ 2 + 4 * X - 4) := by
    dsimp [Q]
    linear_combination (27 * X ^ 2 - 4) * hBase
  have h1 : C (1 : ℚ) * Q ^ 2 * euler (G) = (1134 * T ^ 2 * X ^ 6 - 1377 * T ^ 2 * X ^ 5 - 222 * T ^ 2 * X ^ 4 + 366 * T ^ 2 * X ^ 3 + 8 * T ^ 2 * X ^ 2 - 24 * T ^ 2 * X - 486 * T * X ^ 7 + 486 * T * X ^ 6 - 414 * T * X ^ 5 - 207 * T * X ^ 4 + 180 * T * X ^ 3 + 20 * T * X ^ 2 - 16 * T * X + 729 * X ^ 7 - 1242 * X ^ 6 + 702 * X ^ 5 + 292 * X ^ 4 - 228 * X ^ 3 - 16 * X ^ 2 + 16 * X) := by
    apply jet_step (k := 1) (f := (-27 * T ^ 2 * X ^ 2 + 4 * T ^ 2 + 27 * T * X ^ 3 - 27 * T * X ^ 2 - 4 * T * X + 4 * T - 27 * X ^ 3 + 27 * X ^ 2 + 4 * X - 4)) (h0)
    unfold euler at hTE ⊢
    dsimp [Q] at hTE ⊢
    simp only [euler, map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul,
      derivative_pow, derivative_X, derivative_numeral, map_one_derivative]
    linear_combination (-54 * T * X ^ 2 + 8 * T + 27 * X ^ 3 - 27 * X ^ 2 - 4 * X + 4) * hTE + (-324 * X ^ 5 + 972 * X ^ 4 - 276 * X ^ 3 - 144 * X ^ 2 + 48 * X) * hT
  have h2 : C (1 : ℚ) * Q ^ 3 * euler (euler (G)) = (-43740 * T ^ 2 * X ^ 10 + 37179 * T ^ 2 * X ^ 9 + 41229 * T ^ 2 * X ^ 8 - 59697 * T ^ 2 * X ^ 7 - 10440 * T ^ 2 * X ^ 6 + 22284 * T ^ 2 * X ^ 5 - 80 * T ^ 2 * X ^ 4 - 2760 * T ^ 2 * X ^ 3 + 128 * T ^ 2 * X ^ 2 + 96 * T ^ 2 * X + 8748 * T * X ^ 11 + 30618 * T * X ^ 10 - 16686 * T * X ^ 9 - 23409 * T * X ^ 8 - 6765 * T * X ^ 7 + 6009 * T * X ^ 6 + 4364 * T * X ^ 5 - 44 * T * X ^ 4 - 880 * T * X ^ 3 - 64 * T * X ^ 2 + 64 * T * X - 19683 * X ^ 11 - 3645 * X ^ 10 + 43011 * X ^ 9 - 39150 * X ^ 8 + 12258 * X ^ 7 + 16464 * X ^ 6 - 10904 * X ^ 5 - 1568 * X ^ 4 + 1648 * X ^ 3 - 64 * X) := by
    apply jet_step (k := 2) (f := (1134 * T ^ 2 * X ^ 6 - 1377 * T ^ 2 * X ^ 5 - 222 * T ^ 2 * X ^ 4 + 366 * T ^ 2 * X ^ 3 + 8 * T ^ 2 * X ^ 2 - 24 * T ^ 2 * X - 486 * T * X ^ 7 + 486 * T * X ^ 6 - 414 * T * X ^ 5 - 207 * T * X ^ 4 + 180 * T * X ^ 3 + 20 * T * X ^ 2 - 16 * T * X + 729 * X ^ 7 - 1242 * X ^ 6 + 702 * X ^ 5 + 292 * X ^ 4 - 228 * X ^ 3 - 16 * X ^ 2 + 16 * X)) (h1)
    unfold euler at hTE ⊢
    dsimp [Q] at hTE ⊢
    simp only [euler, map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul,
      derivative_pow, derivative_X, derivative_numeral, map_one_derivative]
    linear_combination (2268 * T * X ^ 6 - 2754 * T * X ^ 5 - 444 * T * X ^ 4 + 732 * T * X ^ 3 + 16 * T * X ^ 2 - 48 * T * X - 486 * X ^ 7 + 486 * X ^ 6 - 414 * X ^ 5 - 207 * X ^ 4 + 180 * X ^ 3 + 20 * X ^ 2 - 16 * X) * hTE + (13608 * X ^ 9 - 57348 * X ^ 8 + 60516 * X ^ 7 - 4140 * X ^ 6 - 15744 * X ^ 5 + 3816 * X ^ 4 + 960 * X ^ 3 - 288 * X ^ 2) * hT
  -- Assemble the differential equation from the cleared derivatives.
  have hODE : X ^ 0 * (C (8 : ℚ) * euler (G) + C (-8 : ℚ) * euler (euler (G))) +
      X ^ 1 * (C (48 : ℚ) * euler (G) + C (12 : ℚ) * euler (euler (G))) +
      X ^ 2 * (C (-34 : ℚ) * G + C (-312 : ℚ) * euler (G) + C (178 : ℚ) * euler (euler (G))) +
      X ^ 3 * (C (108 : ℚ) * G + C (-141 : ℚ) * euler (G) + C (-381 : ℚ) * euler (euler (G))) +
      X ^ 4 * (C (222 : ℚ) * G + C (1365 : ℚ) * euler (G) + C (-741 : ℚ) * euler (euler (G))) +
      X ^ 5 * (C (-306 : ℚ) * G + C (243 : ℚ) * euler (G) + C (2025 : ℚ) * euler (euler (G))) +
      X ^ 6 * (C (-576 : ℚ) * G + C (-1296 : ℚ) * euler (G) + C (-648 : ℚ) * euler (euler (G))) = C (-72 : ℚ) * X ^ 5 + C (60 : ℚ) * X ^ 4 + C (36 : ℚ) * X ^ 3 + C (-6 : ℚ) * X ^ 2 := by
    apply mul_left_cancel₀ (a := C (1 : ℚ) * Q ^ 3)
      (mul_ne_zero (by simp) (pow_ne_zero _ hQ))
    simp only [map_one, map_ofNat, map_neg] at h0 h1 h2 ⊢
    dsimp [Q] at *
    linear_combination ((-576 * X ^ 6 - 306 * X ^ 5 + 222 * X ^ 4 + 108 * X ^ 3 - 34 * X ^ 2) * (27 * X ^ 4 - 81 * X ^ 3 + 23 * X ^ 2 + 12 * X - 4) ^ 2) * h0 + ((-1296 * X ^ 6 + 243 * X ^ 5 + 1365 * X ^ 4 - 141 * X ^ 3 - 312 * X ^ 2 + 48 * X + 8) * (27 * X ^ 4 - 81 * X ^ 3 + 23 * X ^ 2 + 12 * X - 4) ^ 1) * h1 + ((-648 * X ^ 6 + 2025 * X ^ 5 - 741 * X ^ 4 - 381 * X ^ 3 + 178 * X ^ 2 + 12 * X - 8) * (27 * X ^ 4 - 81 * X ^ 3 + 23 * X ^ 2 + 12 * X - 4) ^ 0) * h2
  -- The polynomial on the right has no coefficient at the requested index.
  have hCoeff := congrArg (coeff n) hODE
  simp only [map_add, coeff_X_pow_mul',
    coeff_C_mul, coeff_euler, coeff_X_pow,
    Nat.sub_zero, if_pos (show 0 ≤ n by omega), if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega), if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega), if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 2 by omega), mul_zero, add_zero] at hCoeff
  simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega), Nat.cast_sub (show 5 ≤ n by omega), Nat.cast_sub (show 6 ≤ n by omega)] at hCoeff
  push_cast at hCoeff
  linear_combination hCoeff
