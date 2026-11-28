import OMAStatements.S_oeis_a127275

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
    (hSq : S ^ 2 = 1 - 4 * X)
    (hG : (1 - 4 * X) * G = S - X) :
    derivative ℚ G - C 8 * (X * derivative ℚ G) + C 16 * (X ^ 2 * derivative ℚ G) -
      C 2 * G + C 8 * (X * G) = -C 1 + C 2 * X := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
    norm_num at hc
  have hSqDeriv : 2 * S * derivative ℚ S = -4 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadicalODE : (1 - 4 * X) * derivative ℚ S = -2 * S := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSqDeriv - 2 * derivative ℚ S * hSq
  have hS : S = (1 - 4 * X) * G + X := by
    linear_combination -hG
  have hSDeriv : derivative ℚ S = (1 - 4 * X) * derivative ℚ G - 4 * G + 1 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hS
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  rw [hSDeriv, hS] at hRadicalODE
  rw [map_ofNat C 8, map_ofNat C 16, map_ofNat C 2, map_one]
  linear_combination hRadicalODE

theorem OMA.solution : type_of% @OMA.S_oeis_a127275.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hc := congrArg (coeff (k + 2)) (generating_function_ode S G hSq hG)
  have hne0 : k + 2 ≠ 0 := by omega
  have hne1 : k + 2 ≠ 1 := by omega
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_C, coeff_X_pow_mul,
    coeff_X_derivative, coeff_succ_X_mul, coeff_derivative, coeff_X, hne0, hne1,
    if_false, mul_zero, neg_zero, add_zero] at hc
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
  push_cast at hc ⊢
  linear_combination hc
