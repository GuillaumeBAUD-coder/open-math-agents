import OMAStatements.S_oeis_a166076

open PowerSeries

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private theorem generating_function_ode (S G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 10 * X - 7 * X ^ 2)
    (hG : 2 * (3 + 5 * X + 2 * X ^ 2) * G = 7 + 5 * X - S) :
    C 3 * derivative ℚ G - C 25 * (X * derivative ℚ G) -
      C 69 * (X ^ 2 * derivative ℚ G) - C 55 * (X ^ 3 * derivative ℚ G) -
      C 14 * (X ^ 4 * derivative ℚ G) + C 20 * G -
      C 30 * (X ^ 2 * G) - C 14 * (X ^ 3 * G) = C 20 + C 12 * X := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
    norm_num at hc
  have hSqDerivative : 2 * S * derivative ℚ S = -10 - 14 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadicalODE : (1 - 10 * X - 7 * X ^ 2) * derivative ℚ S = (-5 - 7 * X) * S := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  have hS : S = 7 + 5 * X - 2 * (3 + 5 * X + 2 * X ^ 2) * G := by
    linear_combination hG
  have hSDerivative :
      derivative ℚ S = 5 - 2 * (5 + 4 * X) * G - 2 * (3 + 5 * X + 2 * X ^ 2) * derivative ℚ G := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hS
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  rw [hSDerivative, hS] at hRadicalODE
  rw [map_ofNat C 3, map_ofNat C 25, map_ofNat C 69, map_ofNat C 55,
    map_ofNat C 14, map_ofNat C 20, map_ofNat C 30, map_ofNat C 12]
  apply mul_left_cancel₀ hTwo
  linear_combination -hRadicalODE

private theorem coeff_X_pow_mul_zero (r m : ℕ) (p : ℚ⟦X⟧) (h : m < r) :
    coeff m (X ^ r * p) = 0 := by
  induction r generalizing m p with
  | zero => omega
  | succ r ih =>
    rw [pow_succ', mul_assoc]
    cases m with
    | zero => simp
    | succ m =>
      rw [coeff_succ_X_mul]
      exact ih m p (by omega)

private theorem coeff_k3_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (derivative ℚ G) = ((k : ℚ) + 4) * coeff (k + 4) G := by
  rw [coeff_derivative]
  push_cast
  ring

private theorem coeff_k3_X_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (X * derivative ℚ G) = ((k : ℚ) + 3) * coeff (k + 3) G := by
  rw [coeff_succ_X_mul, coeff_derivative]
  push_cast
  ring

private theorem coeff_k3_X2_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (X ^ 2 * derivative ℚ G) = ((k : ℚ) + 2) * coeff (k + 2) G := by
  rw [show k + 3 = (k + 1) + 2 by omega, coeff_X_pow_mul, coeff_derivative]
  push_cast
  ring

private theorem coeff_k3_X3_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (X ^ 3 * derivative ℚ G) = ((k : ℚ) + 1) * coeff (k + 1) G := by
  rw [coeff_X_pow_mul, coeff_derivative]
  push_cast
  ring

private theorem coeff_k3_X4_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (X ^ 4 * derivative ℚ G) = (k : ℚ) * coeff k G := by
  cases k with
  | zero => simp [coeff_X_pow_mul_zero 4 3 _ (by omega)]
  | succ k =>
    rw [show k + 1 + 3 = k + 4 by omega, coeff_X_pow_mul, coeff_derivative]
    push_cast
    ring

private theorem coeff_k3_X2_mul (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (X ^ 2 * G) = coeff (k + 1) G := by
  rw [show k + 3 = (k + 1) + 2 by omega, coeff_X_pow_mul]

private theorem coeff_k3_X3_mul (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (X ^ 3 * G) = coeff k G := by
  rw [coeff_X_pow_mul]

theorem OMA.solution : type_of% @OMA.S_oeis_a166076.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hode := congrArg (coeff (k + 3)) (generating_function_ode S G hSq hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_C, coeff_X,
    show k + 3 ≠ 0 by omega, show k + 3 ≠ 1 by omega, if_false, mul_zero, add_zero] at hode
  rw [coeff_k3_derivative, coeff_k3_X_derivative, coeff_k3_X2_derivative,
    coeff_k3_X3_derivative, coeff_k3_X4_derivative, coeff_k3_X2_mul,
    coeff_k3_X3_mul] at hode
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  push_cast at hode ⊢
  linear_combination hode
