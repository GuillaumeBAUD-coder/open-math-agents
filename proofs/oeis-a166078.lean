import OMAStatements.S_oeis_a166078

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
    (hSq : S ^ 2 = 1 + 6 * X - 7 * X ^ 2)
    (hG : 2 * (1 - X) * (1 - 2 * X) * G = 3 * (1 - X) - S) :
    derivative ℚ G + C 4 * (X * derivative ℚ G) - C 19 * (X ^ 2 * derivative ℚ G) +
      C 14 * (X ^ 2 * (X * derivative ℚ G)) - C 6 * G - C 4 * (X * G) +
      C 14 * (X ^ 2 * G) = -C 6 := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
    norm_num at hc
  have hSqDerivative : 2 * S * derivative ℚ S = 6 - 14 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadicalODE : (1 + 6 * X - 7 * X ^ 2) * derivative ℚ S = (3 - 7 * X) * S := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  have hS : S = 3 * (1 - X) - 2 * (1 - X) * (1 - 2 * X) * G := by
    linear_combination hG
  have hSDerivative :
      derivative ℚ S = -3 - (-6 + 8 * X) * G - 2 * (1 - X) * (1 - 2 * X) * derivative ℚ G := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hS
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  rw [hSDerivative, hS] at hRadicalODE
  -- Every term of the resulting equation has the factor 2(1 - X).
  have hFactor : (1 - X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    simp at hc
  rw [map_ofNat C 4, map_ofNat C 19, map_ofNat C 14, map_ofNat C 6]
  apply mul_left_cancel₀ (mul_ne_zero hTwo hFactor)
  linear_combination -hRadicalODE

theorem OMA.solution : type_of% @OMA.S_oeis_a166078.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hc := congrArg (coeff (k + 2)) (generating_function_ode S G hSq hG)
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_C, coeff_X_pow_mul,
    coeff_X_derivative, coeff_succ_X_mul, coeff_derivative, Nat.succ_ne_zero,
    if_false, neg_zero] at hc
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  push_cast at hc ⊢
  linear_combination hc
