import OMAStatements.S_oeis_a139376

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

private theorem coeff_X_pow_mul_eq (f : ℚ⟦X⟧) :
    ∀ (m n : ℕ), coeff n (X ^ m * f) = if m ≤ n then coeff (n - m) f else 0
  | 0, n => by simp
  | m + 1, 0 => by rw [pow_succ', mul_assoc]; simp
  | m + 1, n + 1 => by
    rw [pow_succ', mul_assoc, coeff_succ_X_mul, coeff_X_pow_mul_eq f m n]
    simp [Nat.succ_sub_succ]

private theorem generating_function_ode (S c G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X)
    (hc : 2 * X * c = 1 - S)
    (hG : G * ((1 - X ^ 2 * c) * (1 - X - X ^ 2)) = 1) :
    -(X * derivative ℚ G) + C 6 * (X * (X * derivative ℚ G)) -
      C 8 * (X ^ 2 * (X * derivative ℚ G)) - C 2 * (X ^ 3 * (X * derivative ℚ G)) +
      C 9 * (X ^ 4 * (X * derivative ℚ G)) - C 3 * (X ^ 5 * (X * derivative ℚ G)) -
      C 4 * (X ^ 6 * (X * derivative ℚ G)) +
      G - C 6 * (X * G) + C 4 * (X ^ 2 * G) - C 4 * (X ^ 3 * G) +
      C 15 * (X ^ 4 * G) - C 6 * (X ^ 5 * G) - C 14 * (X ^ 6 * G) =
      1 - C 6 * X + X ^ 2 := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    intro h
    have h0 := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at h0
    norm_num at h0
  have hSqDerivative : 2 * S * derivative ℚ S = -4 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadicalODE : (1 - 4 * X) * derivative ℚ S = -2 * S := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  have hXS : X * S = 2 - X - 2 * (1 - X + X ^ 3) * (1 - X - X ^ 2) * G := by
    apply mul_left_cancel₀ hTwo
    linear_combination
      2 * (2 - X - X * S) * hG + G * (1 - X - X ^ 2) * (2 - X - X * S) * X * hc +
        G * (1 - X - X ^ 2) * X ^ 2 * hSq
  have hXSDerivative :
      S + X * derivative ℚ S =
        -1 - (-4 + 12 * X ^ 2 - 8 * X ^ 3 - 10 * X ^ 4) * G -
        2 * (1 - X + X ^ 3) * (1 - X - X ^ 2) * derivative ℚ G := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hXS
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  rw [map_ofNat C 6, map_ofNat C 8, map_ofNat C 2, map_ofNat C 9, map_ofNat C 3,
    map_ofNat C 4, map_ofNat C 15, map_ofNat C 14]
  apply mul_left_cancel₀ hTwo
  linear_combination
    -X * (1 - 4 * X) * hXSDerivative + X ^ 2 * hRadicalODE + (1 - 6 * X) * hXS

theorem OMA.solution : type_of% @OMA.S_oeis_a139376.main := by
  intro S c G hSq _ hc hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have hcoef := congrArg (coeff (k + 6)) (generating_function_ode S c G hSq hc hG)
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow_mul_eq, coeff_succ_X_mul,
    coeff_X_derivative, coeff_derivative, coeff_one, coeff_X, coeff_X_pow] at hcoef
  simp only [show ¬(k + 6 = 0) by omega, show ¬(k + 6 = 1) by omega,
    show ¬(k + 6 = 2) by omega,
    show 2 ≤ k + 6 by omega, show 3 ≤ k + 6 by omega,
    show 4 ≤ k + 6 by omega, show 5 ≤ k + 6 by omega, show 6 ≤ k + 6 by omega,
    show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
    show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega,
    show k + 6 - 5 = k + 1 by omega, show k + 6 - 6 = k by omega,
    ite_true, ite_false] at hcoef ⊢
  push_cast at hcoef ⊢
  linear_combination hcoef
