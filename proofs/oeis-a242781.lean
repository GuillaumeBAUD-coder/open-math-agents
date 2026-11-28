import OMAStatements.S_oeis_a242781

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
    (hSq : S ^ 2 = 1 - 4 * X)
    (hG : G * (4 * X ^ 2 + S * (3 * X + 1) - 5 * X + 1) = 1 - 2 * X - S) :
    let E := X * derivative ℚ G
    (C 3 * E - C 18 * (X ^ 1 * E) + C 22 * (X ^ 2 * E) + C 6 * (X ^ 3 * E) +
        C 7 * (X ^ 4 * E) + C 4 * (X ^ 5 * E)) +
      (C 3 * G - C 18 * (X ^ 1 * G) + C 18 * (X ^ 2 * G) - C 24 * (X ^ 3 * G) +
        C 19 * (X ^ 4 * G) + C 6 * (X ^ 5 * G)) = C 9 * X ^ 2 - C 6 * X ^ 3 - X ^ 4 := by
  dsimp only
  have hSqDerivative : 2 * S * derivative ℚ S = -4 := by
    have hd := congrArg (derivative ℚ) hSq
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hd
    linear_combination hd
  have hRad : (1 - 4 * X) * derivative ℚ S = (-2) * S := by
    apply mul_left_cancel₀ series_two_ne_zero
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  -- Rationalize the generating function before differentiating.
  have hRat :
      (-2 * X * (1 - 4 * X) * (X ^ 2 + 3)) * G =
        (1 - 4 * X) * (X ^ 2 + 1) + (X ^ 2 + 2 * X - 1) * S := by
    apply mul_left_cancel₀ series_two_ne_zero
    linear_combination (4 * X ^ 2 - 5 * X + 1 - (3 * X + 1) * S) * hG +
      ((3 * X + 1) ^ 2 * G + (3 * X + 1)) * hSq
  have hd := congrArg (derivative ℚ) hRat
  simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hd
  simp only [map_ofNat]
  have hP : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff (R := ℚ)) h
    norm_num [map_ofNat] at hc
  apply mul_left_cancel₀ (mul_ne_zero series_two_ne_zero hP)
  linear_combination ((1 - 4 * X) * (X ^ 2 + 2 * X - 1)) * hd +
    (2 * (5 * X ^ 2 + 5 * X - 2)) * hRat + (X ^ 2 + 2 * X - 1) ^ 2 * hRad

theorem OMA.solution : type_of% @OMA.S_oeis_a242781.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have hc := congrArg (coeff (k + 5)) (generating_function_ode S G hSq hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul',
    coeff_X_pow, coeff_X_derivative] at hc
  simp (disch := omega) [show k + 5 - 1 = k + 4 by omega,
    show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega,
    show k + 5 - 4 = k + 1 by omega,
    show k + 5 - 5 = k by omega] at hc
  simp only [show k + 5 - 1 = k + 4 by omega,
    show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega,
    show k + 5 - 4 = k + 1 by omega,
    show k + 5 - 5 = k by omega]
  push_cast at hc ⊢
  linear_combination hc
