import OMAStatements.S_oeis_a114194

open PowerSeries

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private theorem numeral_ne_zero (m : ℕ) [m.AtLeastTwo] :
    (OfNat.ofNat m : ℚ⟦X⟧) ≠ 0 := by
  rw [← map_ofNat C m]
  intro h
  have h0 := congrArg (constantCoeff (R := ℚ)) h
  simp only [constantCoeff_C, map_zero] at h0
  have hm : 2 ≤ m := Nat.AtLeastTwo.prop
  change (m : ℚ) = 0 at h0
  exact (by exact_mod_cast (show m ≠ 0 by omega) : (m : ℚ) ≠ 0) h0

private theorem coeff_X_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff k (X * derivative ℚ G) = (k : ℚ) * coeff k G := by
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative, mul_comm]
    simp only [Nat.cast_add, Nat.cast_one]

private theorem generating_function_ode (S c G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 + 8 * X)
    (hc : -(4 * X * c) = 1 - S)
    (hG : G * (1 + X * (2 - X) * c) = 1) :
    let E := X * derivative ℚ G
    (C 6 * E + C 37 * (X * E) - C 82 * (X ^ 2 * E) + C 47 * (X ^ 3 * E) - C 8 * (X ^ 4 * E)) +
      (C 6 * G + C 8 * (X * G) - C 74 * (X ^ 2 * G) + C 54 * (X ^ 3 * G) - C 12 * (X ^ 4 * G)) = C 6 - C 16 * X - C 2 * X ^ 2 := by
  dsimp only
  have hSqDerivative : 2 * S * derivative ℚ S = 8 := by
    have hd := congrArg (derivative ℚ) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadical : (1 + 8 * X) * derivative ℚ S = (4) * S := by
    apply mul_left_cancel₀ (numeral_ne_zero 2)
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  rw [map_ofNat C 2, map_ofNat C 6, map_ofNat C 8, map_ofNat C 12, map_ofNat C 16, map_ofNat C 37, map_ofNat C 47, map_ofNat C 54, map_ofNat C 74, map_ofNat C 82]
  have hG' : (2 + X + (2 - X) * S) * G = 4 := by
    linear_combination 4 * hG + (2 - X) * G * hc
  have hH : 2 * X * (3 - 4 * X + X ^ 2) * G + (2 + X) = (2 - X) * S := by
    apply mul_left_cancel₀ (numeral_ne_zero 4)
    linear_combination -(2 + X - (2 - X) * S) * hG' - (2 - X) ^ 2 * G * hSq
  have hd := congrArg (derivative ℚ) hH
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
  apply mul_left_cancel₀ (numeral_ne_zero 2)
  linear_combination (2 - X) * (1 + 8 * X) * hd - (7 - 12 * X) * hH + (2 - X) ^ 2 * hRadical

theorem OMA.solution : type_of% @OMA.S_oeis_a114194.main := by
  intro S c G hSq _ hc hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have h := congrArg (coeff (k + 4)) (generating_function_ode S c G hSq hc hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul',
    coeff_X_derivative, coeff_succ_X_mul, coeff_C, coeff_X, coeff_X_pow] at h
  simp (disch := omega) [show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega,
    show k + 4 - 4 = k by omega] at h
  simp only [show k + 4 - 1 = k + 3 by omega,
    show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega,
    show k + 4 - 4 = k by omega]
  simp only [coeff_derivative] at h
  push_cast at h ⊢
  linear_combination h
