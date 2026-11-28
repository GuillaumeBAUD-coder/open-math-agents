import OMAStatements.S_oeis_a162481

open PowerSeries

private lemma derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m, derivative_C]

private lemma coeff_numeral_mul (m n : ℕ) [m.AtLeastTwo] (F : ℚ⟦X⟧) :
    coeff n (no_index (OfNat.ofNat m : ℚ⟦X⟧) * F) = (OfNat.ofNat m : ℚ) * coeff n F := by
  rw [← map_ofNat C m, coeff_C_mul]

private lemma coeff_numeral (m n : ℕ) [m.AtLeastTwo] (hn : n ≠ 0) :
    coeff n (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m, coeff_C, if_neg hn]

private noncomputable def euler (F : ℚ⟦X⟧) : ℚ⟦X⟧ := X * derivative ℚ F

private lemma coeff_euler (F : ℚ⟦X⟧) (n : ℕ) :
    coeff n (euler F) = coeff n F * (n : ℚ) := by
  cases n with
  | zero => simp [euler]
  | succ n => rw [euler, coeff_succ_X_mul, coeff_derivative, Nat.cast_succ]

private lemma coeff_shift_one (F : ℚ⟦X⟧) (n : ℕ) (hn : 1 ≤ n) :
    coeff n (X * F) = coeff (n - 1) F := by
  rw [← pow_one (X : ℚ⟦X⟧), coeff_X_pow_mul', if_pos hn]

theorem OMA.solution : type_of% @OMA.S_oeis_a162481.main := by
  intro T G hT _ hG n hn
  let R : ℚ⟦X⟧ := (1 - X) ^ 3 - 4 * X
  let Rp : ℚ⟦X⟧ := -3 * (1 - X) ^ 2 - 4
  have hdT := congrArg (derivative ℚ) hT
  simp [Derivation.leibniz, smul_eq_mul, derivative_numeral] at hdT
  have hdG := congrArg (derivative ℚ) hG
  simp [Derivation.leibniz, smul_eq_mul, derivative_numeral] at hdG
  have hEuler :
      4 * euler G - 32 * (X * euler G) + 40 * (X ^ 2 * euler G) -
        16 * (X ^ 3 * euler G) + 4 * (X ^ 4 * euler G) +
        4 * G - 24 * (X * G) + 56 * (X ^ 2 * G) - 16 * (X ^ 3 * G) +
        4 * (X ^ 4 * G) - 4 - 8 * X = 0 := by
    unfold euler
    linear_combination -(T * (1 - X) * hdT - (2 * derivative ℚ T * (1 - X) - 3 * T) * hT -
      2 * R * (1 - X) * hdG + (3 * R + (1 - X) * Rp) * hG)
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hc := congrArg (coeff n) hEuler
  simp only [map_add, map_sub, map_zero, coeff_numeral_mul, coeff_numeral _ _ hn0,
    coeff_shift_one _ _ h1, coeff_X_pow_mul', if_pos h2, if_pos h3, if_pos hn,
    coeff_X, coeff_euler] at hc
  simp only [hn1, ↓reduceIte, mul_zero, sub_zero] at hc
  rw [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_sub hn] at hc
  linear_combination hc / 4
