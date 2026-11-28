import OMAStatements.S_oeis_a106272

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
    (hSq : S ^ 2 = 1 - 4 * X)
    (hc : 2 * X * c = 1 - S)
    (hG : G * (1 - X ^ 2) = c * S) :
    let E := X * derivative ℚ G
    (E - C 4 * (X * E) - X ^ 2 * E + C 4 * (X ^ 3 * E)) +
      (G - C 2 * (X * G) - C 3 * (X ^ 2 * G) + C 10 * (X ^ 3 * G)) = 1 - C 4 * X := by
  dsimp only
  have hSqDerivative : 2 * S * derivative ℚ S = -4 := by
    have hd := congrArg (derivative ℚ) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadical : (1 - 4 * X) * derivative ℚ S = (-2) * S := by
    apply mul_left_cancel₀ (numeral_ne_zero 2)
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  rw [map_ofNat C 2, map_ofNat C 3, map_ofNat C 4, map_ofNat C 10]
  have hS : S = 2 * X * (1 - X ^ 2) * G + (1 - 4 * X) := by
    linear_combination -S * hc + hSq - 2 * X * hG
  have hd := congrArg (derivative ℚ) hS
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
  apply mul_left_cancel₀ (numeral_ne_zero 2)
  linear_combination hRadical - (1 - 4 * X) * hd - 2 * hS

theorem OMA.solution : type_of% @OMA.S_oeis_a106272.main := by
  intro S c G hSq _ hc hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have h := congrArg (coeff (k + 3)) (generating_function_ode S c G hSq hc hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul',
    coeff_X_derivative, coeff_succ_X_mul, coeff_one, coeff_X] at h
  simp (disch := omega) [show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega] at h
  simp only [show k + 3 - 1 = k + 2 by omega,
    show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  simp only [coeff_derivative] at h
  push_cast at h ⊢
  linear_combination h
