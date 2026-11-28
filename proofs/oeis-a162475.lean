import OMAStatements.S_oeis_a162475

open PowerSeries

private lemma derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m, derivative_C]

private lemma coeff_numeral_mul (m n : ℕ) [m.AtLeastTwo] (F : ℚ⟦X⟧) :
    coeff n (no_index (OfNat.ofNat m : ℚ⟦X⟧) * F) = (OfNat.ofNat m : ℚ) * coeff n F := by
  rw [← map_ofNat C m, coeff_C_mul]

private lemma series_numeral_ne_zero (m : ℕ) [m.AtLeastTwo] :
    (no_index (OfNat.ofNat m : ℚ⟦X⟧)) ≠ 0 := by
  rw [← map_ofNat (C : ℚ →+* ℚ⟦X⟧) m, ← map_zero (C : ℚ →+* ℚ⟦X⟧)]
  exact fun h => Nat.cast_ne_zero.mpr (NeZero.ne m) (C_injective h)

private noncomputable def euler (F : ℚ⟦X⟧) : ℚ⟦X⟧ := X * derivative ℚ F

private lemma coeff_euler (F : ℚ⟦X⟧) (n : ℕ) :
    coeff n (euler F) = coeff n F * (n : ℚ) := by
  cases n with
  | zero => simp [euler]
  | succ n => rw [euler, coeff_succ_X_mul, coeff_derivative, Nat.cast_succ]

private lemma coeff_shift_one (F : ℚ⟦X⟧) (n : ℕ) (hn : 1 ≤ n) :
    coeff n (X * F) = coeff (n - 1) F := by
  rw [← pow_one (X : ℚ⟦X⟧), coeff_X_pow_mul', if_pos hn]

private lemma ne_zero_of_coeff_zero_ne_zero {F : ℚ⟦X⟧} (h : coeff 0 F ≠ 0) : F ≠ 0 :=
  fun h0 => h (by simp [h0])

theorem OMA.solution : type_of% @OMA.S_oeis_a162475.main := by
  intro T G hT _ hG n hn
  let A : ℚ⟦X⟧ := (1 - X) ^ 4 - 4 * X
  let H : ℚ⟦X⟧ := (1 - X) ^ 4 - 2 * X * G
  have hH : H = (1 - X) ^ 4 * T := by
    dsimp [H]
    linear_combination -hG
  have hH0 : coeff 0 H = 1 := by
    simp [H]
  have hHne : H ≠ 0 := ne_zero_of_coeff_zero_ne_zero (by rw [hH0]; norm_num)
  have h1Xne : (1 - X : ℚ⟦X⟧) ≠ 0 := ne_zero_of_coeff_zero_ne_zero (by simp)
  have hH2 : H ^ 2 = (1 - X) ^ 4 * A := by
    dsimp [A]
    linear_combination (H + (1 - X) ^ 4 * T) * hH + (1 - X) ^ 4 * hT
  have hd : 2 * H * derivative ℚ H =
      (1 - X) ^ 3 * (-4 * A + (1 - X) * derivative ℚ A) := by
    have h := congrArg (derivative ℚ) hH2
    simp [Derivation.leibniz, smul_eq_mul] at h
    linear_combination h
  have hd1 : 2 * (1 - X) * A * derivative ℚ H =
      (-4 * A + (1 - X) * derivative ℚ A) * H := by
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 3 h1Xne) hHne)
    linear_combination (1 - X) ^ 4 * A * hd -
      (1 - X) ^ 3 * (-4 * A + (1 - X) * derivative ℚ A) * hH2
  have hderivA : derivative ℚ A = -4 * (1 - X) ^ 3 - 4 := by
    dsimp [A]
    simp [derivative_numeral]
  have hderivH : derivative ℚ H = -4 * (1 - X) ^ 3 - 2 * G - 2 * X * derivative ℚ G := by
    dsimp [H]
    simp [Derivation.leibniz, smul_eq_mul, derivative_numeral]
    ring
  rw [hderivA, hderivH] at hd1
  have hEuler : euler G - 9 * (X * euler G) + 14 * (X ^ 2 * euler G) -
      10 * (X ^ 3 * euler G) + 5 * (X ^ 4 * euler G) - X ^ 5 * euler G +
      G - 3 * (X * G) - 12 * (X ^ 2 * G) + 14 * (X ^ 3 * G) -
      11 * (X ^ 4 * G) + 3 * (X ^ 5 * G) -
      (1 - X - 6 * X ^ 2 + 14 * X ^ 3 - 11 * X ^ 4 + 3 * X ^ 5) = 0 := by
    apply mul_left_cancel₀ (neg_ne_zero.mpr (series_numeral_ne_zero 4))
    unfold euler
    dsimp [A, H] at hd1
    linear_combination hd1
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h4 : 4 ≤ n := by omega
  have h5 : 5 ≤ n := by omega
  have hc := congrArg (coeff n) hEuler
  simp only [map_add, map_sub, map_zero, coeff_numeral_mul, coeff_shift_one _ _ h1,
    coeff_X_pow_mul', if_pos h2, if_pos h3, if_pos h4, if_pos h5, coeff_euler,
    coeff_one, coeff_X, coeff_X_pow,
    if_neg (by omega : n ≠ 0), if_neg (by omega : n ≠ 1),
    if_neg (by omega : n ≠ 2), if_neg (by omega : n ≠ 3),
    if_neg (by omega : n ≠ 4), if_neg (by omega : n ≠ 5)] at hc
  rw [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_sub h4, Nat.cast_sub h5] at hc
  linear_combination hc
