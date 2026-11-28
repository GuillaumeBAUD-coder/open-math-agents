import OMAStatements.S_oeis_a136304

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
    simp [Nat.succ_le_succ_iff, Nat.succ_sub_succ]

private theorem generating_function_ode (S G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X)
    (hG : 2 * X * (1 - 3 * X + 2 * X ^ 2 - X ^ 3) * G = (1 - X) ^ 2 * (1 - S)) :
    X * derivative ℚ G - C 8 * (X * (X * derivative ℚ G)) +
      C 21 * (X ^ 2 * (X * derivative ℚ G)) - C 23 * (X ^ 3 * (X * derivative ℚ G)) +
      C 13 * (X ^ 4 * (X * derivative ℚ G)) - C 4 * (X ^ 5 * (X * derivative ℚ G)) +
      G - C 7 * (X * G) + C 18 * (X ^ 2 * G) - C 20 * (X ^ 3 * G) +
      C 20 * (X ^ 4 * G) - C 6 * (X ^ 5 * G) =
      1 - C 3 * X + C 3 * X ^ 2 - X ^ 3 := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
    norm_num at hc
  have hSqDerivative : 2 * S * derivative ℚ S = -4 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadicalODE : (1 - 4 * X) * derivative ℚ S = -2 * S := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  have hS : (1 - X) ^ 2 * S =
      (1 - X) ^ 2 - 2 * X * (1 - 3 * X + 2 * X ^ 2 - X ^ 3) * G := by
    linear_combination hG
  have hSDerivative :
      -2 * (1 - X) * S + (1 - X) ^ 2 * derivative ℚ S =
        -2 * (1 - X) - (2 - 12 * X + 12 * X ^ 2 - 8 * X ^ 3) * G -
        2 * X * (1 - 3 * X + 2 * X ^ 2 - X ^ 3) * derivative ℚ G := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hS
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  rw [map_ofNat C 8, map_ofNat C 21, map_ofNat C 23, map_ofNat C 13, map_ofNat C 4,
    map_ofNat C 7, map_ofNat C 18, map_ofNat C 20, map_ofNat C 6, map_ofNat C 3]
  apply mul_left_cancel₀ hTwo
  linear_combination
    (1 - X) * (1 - 4 * X) * hSDerivative - (1 - X) ^ 3 * hRadicalODE +
      2 * (2 - 5 * X) * hS

theorem OMA.solution : type_of% @OMA.S_oeis_a136304.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have hc := congrArg (coeff (k + 5)) (generating_function_ode S G hSq hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul_eq, coeff_succ_X_mul,
    coeff_X_derivative, coeff_derivative, coeff_one, coeff_X, coeff_X_pow] at hc
  simp only [show ¬(k + 5 = 0) by omega, show ¬(k + 5 = 1) by omega,
    show ¬(k + 5 = 2) by omega, show ¬(k + 5 = 3) by omega,
    show 2 ≤ k + 5 by omega, show 3 ≤ k + 5 by omega,
    show 4 ≤ k + 5 by omega, show 5 ≤ k + 5 by omega,
    show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
    show k + 5 - 5 = k by omega, ite_true, ite_false] at hc ⊢
  push_cast at hc ⊢
  linear_combination hc
