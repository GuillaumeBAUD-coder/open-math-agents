import OMAStatements.S_oeis_a129147

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

private theorem generating_function_ode (S G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X - 8 * X ^ 2)
    (hG : 2 * (X + 2 * X ^ 2) * G = 1 - S) :
    X * derivative ℚ G - C 2 * (X * (X * derivative ℚ G)) -
      C 16 * (X ^ 2 * (X * derivative ℚ G)) - C 16 * (X ^ 3 * (X * derivative ℚ G)) +
      G + C 2 * (X * G) - C 12 * (X ^ 2 * G) - C 16 * (X ^ 3 * G) = 1 + C 4 * X := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
    norm_num at hc
  have hSqDerivative : 2 * S * derivative ℚ S = -4 - 16 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadicalODE : (1 - 4 * X - 8 * X ^ 2) * derivative ℚ S = (-2 - 8 * X) * S := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  have hS : S = 1 - 2 * (X + 2 * X ^ 2) * G := by
    linear_combination hG
  have hSDerivative :
      derivative ℚ S = -(2 * (1 + 4 * X) * G) - 2 * (X + 2 * X ^ 2) * derivative ℚ G := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hS
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  rw [hSDerivative, hS] at hRadicalODE
  rw [map_ofNat C 2, map_ofNat C 16, map_ofNat C 12, map_ofNat C 4]
  apply mul_left_cancel₀ hTwo
  linear_combination -hRadicalODE

theorem OMA.solution : type_of% @OMA.S_oeis_a129147.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hc := congrArg (coeff (k + 3)) (generating_function_ode S G hSq hG)
  have h2 : ∀ φ : ℚ⟦X⟧, coeff (k + 3) (X ^ 2 * φ) = coeff (k + 1) φ :=
    fun φ => coeff_X_pow_mul φ 2 (k + 1)
  simp only [map_add, map_sub, coeff_C_mul, h2, coeff_X_pow_mul,
    coeff_X_derivative, coeff_succ_X_mul, coeff_derivative, coeff_one, coeff_X,
    Nat.succ_ne_zero, show k + 3 ≠ 1 by omega, if_false, mul_zero, add_zero] at hc
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  push_cast at hc ⊢
  linear_combination hc
