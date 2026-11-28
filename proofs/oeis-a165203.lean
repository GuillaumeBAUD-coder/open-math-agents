import OMAStatements.S_oeis_a165203

open PowerSeries

private lemma derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m, derivative_C]

private lemma coeff_numeral_mul (m n : ℕ) [m.AtLeastTwo] (F : ℚ⟦X⟧) :
    coeff n (no_index (OfNat.ofNat m : ℚ⟦X⟧) * F) = (OfNat.ofNat m : ℚ) * coeff n F := by
  rw [← map_ofNat C m, coeff_C_mul]

private lemma coeff_numeral_of_pos (m n : ℕ) [m.AtLeastTwo] (hn : 0 < n) :
    coeff n (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m, coeff_C, if_neg hn.ne']

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

theorem OMA.solution : type_of% @OMA.S_oeis_a165203.main := by
  intro S c G hS hS0 hc hG n hn
  have hSne : S ≠ 0 := ne_zero_of_coeff_zero_ne_zero (by rw [hS0]; norm_num)
  have hXne : (X : ℚ⟦X⟧) ≠ 0 := fun h => by simpa using congrArg (coeff 1) h
  have hc3 : 8 * X ^ 3 * c ^ 3 = 4 * ((1 - 3 * X) - (1 - X) * S) := by
    linear_combination ((2 * X * c) ^ 2 + (2 * X * c) * (1 - S) + (1 - S) ^ 2) * hc +
      (3 - S) * hS
  have hG_S : 4 * X * ((-1 + 3 * X + 2 * X ^ 2) + (1 - X) * S) * G =
      4 * (1 + X) * ((1 - 3 * X) - (1 - X) * S) := by
    linear_combination 8 * X ^ 3 * hG + (X * G + (1 + X)) * hc3
  have hGS : 2 * X * (-1 + 4 * X + X ^ 2) * G =
      (1 - 4 * X - 5 * X ^ 2) + (-1 + X ^ 2) * S := by
    apply mul_left_cancel₀ (mul_ne_zero (series_numeral_ne_zero 8) (pow_ne_zero 2 hXne))
    linear_combination ((-1 + 3 * X + 2 * X ^ 2) - (1 - X) * S) * hG_S +
      (4 * X * (1 - X) ^ 2 * G + 4 * (1 + X) * (1 - X) ^ 2) * hS
  have hdS : (1 - 4 * X) * derivative ℚ S = -2 * S := by
    have h := congrArg (derivative ℚ) hS
    simp [Derivation.leibniz, smul_eq_mul, derivative_numeral] at h
    apply mul_left_cancel₀ (mul_ne_zero (series_numeral_ne_zero 2) hSne)
    linear_combination (1 - 4 * X) * h - 2 * (-2) * hS
  have hdGS := congrArg (derivative ℚ) hGS
  simp [Derivation.leibniz, smul_eq_mul, derivative_numeral] at hdGS
  let L : ℚ⟦X⟧ := (2 - 16 * X + 28 * X ^ 2 + 24 * X ^ 3 - 30 * X ^ 4 - 8 * X ^ 5) * euler G +
    (2 - 20 * X + 44 * X ^ 2 + 8 * X ^ 3 + 18 * X ^ 4 - 4 * X ^ 5) * G -
    (2 - 16 * X ^ 2 - 24 * X ^ 3 - 10 * X ^ 4)
  have hL : L = 0 := by
    dsimp [L]
    unfold euler
    linear_combination (1 - 4 * X) * (-1 + X ^ 2) * hdGS + (-1 + X ^ 2) ^ 2 * hdS +
      (-2 - 2 * X + 10 * X ^ 2) * hGS
  have heL : euler L = 0 := by
    rw [hL]
    simp [euler]
  have hEuler : 5 * euler (euler G) + 5 * (X * euler (euler G)) - 285 * (X ^ 2 * euler (euler G)) +
      695 * (X ^ 3 * euler (euler G)) + 180 * (X ^ 4 * euler (euler G)) -
      26 * euler G + 84 * (X * euler G) - 68 * (X ^ 2 * euler G) +
      496 * (X ^ 3 * euler G) + 514 * (X ^ 4 * euler G) -
      31 * G + 141 * (X * G) + 247 * (X ^ 2 * G) - 561 * (X ^ 3 * G) + 212 * (X ^ 4 * G) -
      (-31 - 119 * X + 137 * X ^ 2 + 305 * X ^ 3) = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero (series_numeral_ne_zero 8)
      (ne_zero_of_coeff_zero_ne_zero (by simp) : (1 - X ^ 2 : ℚ⟦X⟧) ≠ 0))
    have heL1 : euler L =
        (2 - 16 * X + 28 * X ^ 2 + 24 * X ^ 3 - 30 * X ^ 4 - 8 * X ^ 5) * euler (euler G) +
        ((-16 * X + 56 * X ^ 2 + 72 * X ^ 3 - 120 * X ^ 4 - 40 * X ^ 5) +
          (2 - 20 * X + 44 * X ^ 2 + 8 * X ^ 3 + 18 * X ^ 4 - 4 * X ^ 5)) * euler G +
        (-20 * X + 88 * X ^ 2 + 24 * X ^ 3 + 72 * X ^ 4 - 20 * X ^ 5) * G -
        (-32 * X ^ 2 - 72 * X ^ 3 - 40 * X ^ 4) := by
      dsimp [L]
      unfold euler
      simp [Derivation.leibniz, smul_eq_mul, derivative_numeral]
      ring
    linear_combination (20 + 180 * X) * (heL - heL1) + (-124 - 476 * X) * hL
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h4 : 4 ≤ n := by omega
  have hc1 := congrArg (coeff n) hEuler
  simp only [map_add, map_sub, map_neg, map_zero, coeff_numeral_mul, coeff_numeral_of_pos _ _ h1,
    coeff_shift_one _ _ h1, coeff_X_pow_mul', if_pos h2, if_pos h3, if_pos h4, coeff_euler,
    coeff_X, coeff_X_pow,
    if_neg (by omega : n ≠ 1), if_neg (by omega : n ≠ 2), if_neg (by omega : n ≠ 3)] at hc1
  rw [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_sub h4] at hc1
  linear_combination hc1
