import OMAStatements.S_oeis_a116409

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
    (hSq : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : 2 * (1 - X) * (1 - 2 * X - 3 * X ^ 2) * G = 1 - X - 2 * X ^ 2 + S) :
    derivative ℚ G - C 6 * (X * derivative ℚ G) +
      C 8 * (X * (X * derivative ℚ G)) + C 6 * (X * (X * (X * derivative ℚ G))) -
      C 9 * (X * (X * (X * (X * derivative ℚ G)))) - C 2 * G + C 6 * (X * G) +
      C 6 * (X * (X * G)) - C 18 * (X * (X * (X * G))) = C 3 * X ^ 2 := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
    norm_num at hc
  have hSqDerivative : 2 * S * derivative ℚ S = -2 - 6 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadicalODE : (1 - 2 * X - 3 * X ^ 2) * derivative ℚ S = (-1 - 3 * X) * S := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  have hS : S = 2 * (1 - X) * (1 - 2 * X - 3 * X ^ 2) * G - (1 - X - 2 * X ^ 2) := by
    linear_combination -hG
  have hSDerivative :
      derivative ℚ S =
        2 * (1 - X) * (1 - 2 * X - 3 * X ^ 2) * derivative ℚ G +
          (-6 - 4 * X + 18 * X ^ 2) * G - (-1 - 4 * X) := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hS
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  rw [hSDerivative, hS] at hRadicalODE
  have hFactor : (1 + X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    simp at hc
  rw [map_ofNat C 6, map_ofNat C 8, map_ofNat C 9, map_ofNat C 2,
    map_ofNat C 18, map_ofNat C 3]
  apply mul_left_cancel₀ (mul_ne_zero hTwo hFactor)
  linear_combination hRadicalODE

theorem OMA.solution : type_of% @OMA.S_oeis_a116409.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hc := congrArg (coeff (k + 3)) (generating_function_ode S G hSq hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_derivative,
    coeff_succ_X_mul, coeff_derivative, show k + 3 ≠ 2 by omega,
    coeff_X_pow, if_false, mul_zero] at hc
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  push_cast at hc ⊢
  linear_combination hc
