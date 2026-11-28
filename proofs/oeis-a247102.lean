import OMAStatements.S_oeis_a247102

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

private theorem series_two_ne_zero : (2 : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have hc := congrArg (constantCoeff (R := ℚ)) h
  norm_num [map_ofNat] at hc

private theorem generating_function_ode (S G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 6 * X - 3 * X ^ 2)
    (hG : G * ((4 * X ^ 2 + 4 * X) * S) = 6 * X + 2 - 2 * (2 * X + 1) * S) :
    let E := X * derivative ℚ G
    (E - C 2 * (X ^ 1 * E) - C 24 * (X ^ 2 * E) - C 30 * (X ^ 3 * E) - C 9 * (X ^ 4 * E)) +
      (G - C 7 * (X ^ 1 * G) - C 27 * (X ^ 2 * G) - C 45 * (X ^ 3 * G) - C 18 * (X ^ 4 * G)) = C 2 + C 6 * X ^ 1 + C 15 * X ^ 2 + C 9 * X ^ 3 := by
  dsimp only
  have hSqDerivative : 2 * S * derivative ℚ S = -6 - 6 * X := by
    have hd := congrArg (derivative ℚ) hSq
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hd
    linear_combination hd
  have hRad : (1 - 6 * X - 3 * X ^ 2) * derivative ℚ S = (-3 - 3 * X) * S := by
    apply mul_left_cancel₀ series_two_ne_zero
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  -- Rationalize the generating function before differentiating.
  have hRat :
      (-2 * X * (X + 1) * (1 - 6 * X - 3 * X ^ 2)) * G =
        (2 * X + 1) * (1 - 6 * X - 3 * X ^ 2) - (3 * X + 1) * S := by
    apply mul_left_cancel₀ series_two_ne_zero
    linear_combination -S * hG + ((4 * X ^ 2 + 4 * X) * G + 2 * (2 * X + 1)) * hSq
  have hd := congrArg (derivative ℚ) hRat
  simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hd
  simp only [map_ofNat]
  have hP : (1 - 6 * X - 3 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff (R := ℚ)) h
    norm_num [map_ofNat] at hc
  apply mul_left_cancel₀ (mul_ne_zero series_two_ne_zero hP)
  linear_combination (-(1 - 6 * X - 3 * X ^ 2) * (3 * X + 1)) * hd -
    (6 * X * (3 * X + 5)) * hRat + (3 * X + 1) ^ 2 * hRad

theorem OMA.solution : type_of% @OMA.S_oeis_a247102.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hc := congrArg (coeff (k + 4)) (generating_function_ode S G hSq hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_C, coeff_X_pow_mul',
    coeff_X_pow, coeff_X_derivative] at hc
  simp (disch := omega) [show k + 4 - 1 = k + 3 by omega,
    show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega,
    show k + 4 - 4 = k by omega] at hc
  simp only [show k + 4 - 1 = k + 3 by omega,
    show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega,
    show k + 4 - 4 = k by omega]
  push_cast at hc ⊢
  linear_combination hc
