import OMAStatements.S_oeis_a025577

open PowerSeries

private lemma derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m, derivative_C]

private lemma coeff_numeral_mul (m n : ℕ) [m.AtLeastTwo] (F : ℚ⟦X⟧) :
    coeff n (no_index (OfNat.ofNat m : ℚ⟦X⟧) * F) = (OfNat.ofNat m : ℚ) * coeff n F := by
  rw [← map_ofNat C m, coeff_C_mul]

private lemma series_two_ne_zero : (2 : ℚ⟦X⟧) ≠ 0 := by
  rw [← map_ofNat (C : ℚ →+* ℚ⟦X⟧) 2, ← map_zero (C : ℚ →+* ℚ⟦X⟧)]
  exact fun h => two_ne_zero (C_injective h)

private noncomputable def euler (F : ℚ⟦X⟧) : ℚ⟦X⟧ := X * derivative ℚ F

private lemma coeff_euler (F : ℚ⟦X⟧) (n : ℕ) :
    coeff n (euler F) = coeff n F * (n : ℚ) := by
  cases n with
  | zero => simp [euler]
  | succ n => rw [euler, coeff_succ_X_mul, coeff_derivative, Nat.cast_succ]

private lemma coeff_shift_one (F : ℚ⟦X⟧) (n : ℕ) (hn : 1 ≤ n) :
    coeff n (X * F) = coeff (n - 1) F := by
  rw [← pow_one (X : ℚ⟦X⟧), coeff_X_pow_mul', if_pos hn]

theorem OMA.solution : type_of% @OMA.S_oeis_a025577.main := by
  intro T G hT hT0 hG n hn
  have hFactor : (1 - X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff (R := ℚ)) h
    simp at hc
  have hGne : G ≠ 0 := by
    intro h
    have hc := congrArg (coeff 1) hG
    simp [h, hT0] at hc
  have hSq : (1 - X) ^ 2 * (1 - 3 * X) * G ^ 2 = X ^ 2 * (1 + X) := by
    linear_combination (1 - 3 * X) * (G * (1 - X) + X * T) * hG + X ^ 2 * hT
  have hd := congrArg (derivative ℚ) hSq
  simp [Derivation.leibniz, smul_eq_mul, derivative_numeral] at hd
  have hEuler : G - 5 * (X ^ 2 * G) - euler G + 3 * (X * euler G) +
      X ^ 2 * euler G - 3 * (X ^ 3 * euler G) = 0 := by
    unfold euler
    apply mul_left_cancel₀ (mul_ne_zero
      (mul_ne_zero series_two_ne_zero hFactor) hGne)
    linear_combination (2 + 3 * X) * hSq - X * (1 + X) * hd
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have hc := congrArg (coeff n) hEuler
  simp only [map_add, map_sub, map_zero, coeff_numeral_mul, coeff_shift_one _ _ h1,
    coeff_X_pow_mul', if_pos h2, if_pos hn, coeff_euler] at hc
  rw [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub hn] at hc
  linear_combination hc
