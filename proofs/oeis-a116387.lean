import OMAStatements.S_oeis_a116387

open PowerSeries

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private noncomputable def theta1 (G : ℚ⟦X⟧) : ℚ⟦X⟧ := X * derivative ℚ G
private noncomputable def theta2 (G : ℚ⟦X⟧) : ℚ⟦X⟧ := X * derivative ℚ (theta1 G)

private theorem coeff_theta1 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff k (theta1 G) = (k : ℚ) * coeff k G := by
  unfold theta1
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative, mul_comm]
    simp only [Nat.cast_add, Nat.cast_one]

private theorem coeff_theta2 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff k (theta2 G) = (k : ℚ) ^ 2 * coeff k G := by
  unfold theta2
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative, coeff_theta1]
    push_cast
    ring

private theorem coeff_X_pow_mul_le {d n : ℕ} (h : d ≤ n) (f : ℚ⟦X⟧) :
    coeff n (X ^ d * f) = coeff (n - d) f := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [coeff_X_pow_mul, Nat.add_sub_cancel]

private theorem coeff_X_mul_ge1 {n : ℕ} (h : 1 ≤ n) (f : ℚ⟦X⟧) :
    coeff n (X * f) = coeff (n - 1) f := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [coeff_succ_X_mul, Nat.add_sub_cancel]

private theorem generating_function_ode (S M G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hM : 2 * X ^ 2 * M = 1 - X - S)
    (hG : G * (S * (2 - M)) = 1) :
    C 17 * theta2 G + C 17 * (X * theta2 G) - C 391 * (X ^ 2 * theta2 G) -
        C 17 * (X ^ 3 * theta2 G) + C 1394 * (X ^ 4 * theta2 G) +
        C 1020 * (X ^ 5 * theta2 G) +
      (-(C 142 * theta1 G) + C 129 * (X * theta1 G) + C 924 * (X ^ 2 * theta1 G) -
        C 705 * (X ^ 3 * theta1 G) + C 1534 * (X ^ 4 * theta1 G) +
        C 3300 * (X ^ 5 * theta1 G)) +
      (C 250 * (X * G) + C 504 * (X ^ 2 * G) - C 70 * (X ^ 3 * G) +
        C 2280 * (X ^ 5 * G)) =
      -(C 216 * (X ^ 2 * C 1)) + C 30 * (X ^ 3 * C 1) := by
  have h2X2_ne : (2 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (coeff 2) h
    rw [← map_ofNat C 2, coeff_C_mul, map_zero] at hc
    simp at hc
  have h2U_ne : (2 * (1 - 2 * X - 3 * X ^ 2) : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    rw [← map_ofNat C 2, ← map_ofNat C 3] at hc
    simp at hc
  have h2K2_ne : (2 * (1 - 2 * X - 4 * X ^ 2) ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    rw [← map_ofNat C 2, ← map_ofNat C 4] at hc
    simp at hc
  have hAlg0 : G * S * (4 * X ^ 2 + X - 1 + S) = 2 * X ^ 2 := by
    linear_combination 2 * X ^ 2 * hG + G * S * hM
  have hKSG : 2 * (1 - 2 * X - 4 * X ^ 2) * S * G = S + (1 - X - 4 * X ^ 2) := by
    apply mul_left_cancel₀ h2X2_ne
    linear_combination (S + (1 - X - 4 * X ^ 2)) * hAlg0 - G * S * hSq
  set H : ℚ⟦X⟧ := 2 * (1 - 2 * X - 4 * X ^ 2) * G - 1 with hH_def
  have hH : S * H = 1 - X - 4 * X ^ 2 := by
    rw [hH_def]
    linear_combination hKSG
  have h0 : (1 - 2 * X - 3 * X ^ 2) * H = (1 - X - 4 * X ^ 2) * S := by
    linear_combination S * hH - H * hSq
  have hSqDeriv : 2 * S * derivative ℚ S = -2 - 6 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hUSDeriv : 2 * (1 - 2 * X - 3 * X ^ 2) * derivative ℚ S = (-2 - 6 * X) * S := by
    linear_combination S * hSqDeriv - 2 * derivative ℚ S * hSq
  have hHDeriv0 : S * derivative ℚ H + derivative ℚ S * H = -1 - 8 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hH
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have h1 :
      2 * (1 - 2 * X - 3 * X ^ 2) * derivative ℚ H + (-2 - 6 * X) * H =
        2 * (-1 - 8 * X) * S := by
    linear_combination 2 * S * hHDeriv0 - H * hSqDeriv - 2 * derivative ℚ H * hSq
  have hH1Deriv :
      2 * (1 - 2 * X - 3 * X ^ 2) * derivative ℚ (derivative ℚ H) +
          3 * (-2 - 6 * X) * derivative ℚ H - 6 * H =
        -16 * S + 2 * (-1 - 8 * X) * derivative ℚ S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) h1
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have h2 :
      2 * (1 - 2 * X - 3 * X ^ 2) ^ 2 * derivative ℚ (derivative ℚ H) +
          3 * (1 - 2 * X - 3 * X ^ 2) * (-2 - 6 * X) * derivative ℚ H -
          6 * (1 - 2 * X - 3 * X ^ 2) * H =
        (-16 * (1 - 2 * X - 3 * X ^ 2) + (-1 - 8 * X) * (-2 - 6 * X)) * S := by
    linear_combination (1 - 2 * X - 3 * X ^ 2) * hH1Deriv + (-1 - 8 * X) * hUSDeriv
  let A_H : ℚ⟦X⟧ :=
    17 * X ^ 2 - 17 * X ^ 3 - 493 * X ^ 4 + 697 * X ^ 5 + 2992 * X ^ 6 -
      1700 * X ^ 7 - 7616 * X ^ 8 - 4080 * X ^ 9
  let B_H : ℚ⟦X⟧ :=
    -125 * X + 464 * X ^ 2 + 1081 * X ^ 3 - 3664 * X ^ 4 - 4084 * X ^ 5 +
      6656 * X ^ 6 + 6032 * X ^ 7 - 960 * X ^ 8
  let C_H : ℚ⟦X⟧ :=
    -432 * X ^ 2 + 1788 * X ^ 3 + 1488 * X ^ 4 - 7152 * X ^ 5 - 5952 * X ^ 6 + 960 * X ^ 7
  have hH_ode : A_H * derivative ℚ (derivative ℚ H) + B_H * derivative ℚ H + C_H * H = 0 := by
    apply mul_left_cancel₀ h2U_ne
    let m2 : ℚ⟦X⟧ :=
      17 * X ^ 2 + 17 * X ^ 3 - 408 * X ^ 4 - 68 * X ^ 5 + 1632 * X ^ 6 + 1360 * X ^ 7
    let m1 : ℚ⟦X⟧ :=
      -125 * X + 515 * X ^ 2 + 1285 * X ^ 3 - 4735 * X ^ 4 - 7960 * X ^ 5 +
        10940 * X ^ 6 + 24800 * X ^ 7 + 11280 * X ^ 8
    let m0 : ℚ⟦X⟧ :=
      -250 * X - 982 * X ^ 2 + 8148 * X ^ 3 + 7048 * X ^ 4 - 32592 * X ^ 5 -
        44192 * X ^ 6 - 12480 * X ^ 7
    dsimp only [A_H, B_H, C_H, m2, m1, m0]
    linear_combination m2 * h2 + m1 * h1 + m0 * h0
  have hHd1 :
      derivative ℚ H = 2 * (1 - 2 * X - 4 * X ^ 2) * derivative ℚ G + 2 * (-2 - 8 * X) * G := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hH_def
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hHd2 :
      derivative ℚ (derivative ℚ H) =
        2 * (1 - 2 * X - 4 * X ^ 2) * derivative ℚ (derivative ℚ G) +
          4 * (-2 - 8 * X) * derivative ℚ G - 16 * G := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hHd1
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hθ2G : theta2 G = X * derivative ℚ G + X ^ 2 * derivative ℚ (derivative ℚ G) := by
    unfold theta2 theta1
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  unfold theta1
  rw [map_ofNat C 17, map_ofNat C 391, map_ofNat C 1394, map_ofNat C 1020,
    map_ofNat C 142, map_ofNat C 129, map_ofNat C 924, map_ofNat C 705,
    map_ofNat C 1534, map_ofNat C 3300, map_ofNat C 250, map_ofNat C 504,
    map_ofNat C 70, map_ofNat C 2280, map_ofNat C 216, map_ofNat C 30, map_one]
  apply mul_left_cancel₀ h2K2_ne
  rw [hθ2G]
  dsimp only [A_H, B_H, C_H] at hH_ode ⊢
  rw [hH_def] at hH_ode
  linear_combination hH_ode -
    (17 * X ^ 2 - 17 * X ^ 3 - 493 * X ^ 4 + 697 * X ^ 5 + 2992 * X ^ 6 -
      1700 * X ^ 7 - 7616 * X ^ 8 - 4080 * X ^ 9) * hHd2 -
    (-125 * X + 464 * X ^ 2 + 1081 * X ^ 3 - 3664 * X ^ 4 - 4084 * X ^ 5 +
      6656 * X ^ 6 + 6032 * X ^ 7 - 960 * X ^ 8) * hHd1

theorem OMA.solution : type_of% @OMA.S_oeis_a116387.main := by
  intro S M G hSq _ hM hG n hn
  have hcoeff := congrArg (coeff n) (generating_function_ode S M G hSq hM hG)
  have hne2 : n - 2 ≠ 0 := by omega
  have hne3 : n - 3 ≠ 0 := by omega
  simp only [map_add, map_sub, map_neg, coeff_C_mul,
    coeff_X_pow_mul_le (show 2 ≤ n by omega),
    coeff_X_pow_mul_le (show 3 ≤ n by omega),
    coeff_X_pow_mul_le (show 4 ≤ n by omega),
    coeff_X_pow_mul_le (show 5 ≤ n by omega),
    coeff_X_mul_ge1 (show 1 ≤ n by omega),
    coeff_C, hne2, hne3, if_false, mul_zero, neg_zero, add_zero] at hcoeff
  simp only [coeff_theta1, coeff_theta2] at hcoeff
  simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega),
    Nat.cast_sub (show 5 ≤ n by omega)] at hcoeff
  push_cast at hcoeff ⊢
  linear_combination hcoeff
