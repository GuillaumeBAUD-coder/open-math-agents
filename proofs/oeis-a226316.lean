import OMAStatements.S_oeis_a226316

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

private theorem two_ne : (2 : ℚ⟦X⟧) ≠ 0 := by
  rw [← map_ofNat C 2]
  intro h
  have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
  change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
  norm_num at hc

private theorem generating_function_ode (S G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 8 * X + 8 * X ^ 2)
    (hG : (2 * G - 1) * (1 + S) = 2) :
    C 1 * (X * derivative ℚ G) + C (-9) * (X ^ 1 * (X * derivative ℚ G)) +
      C 16 * (X ^ 2 * (X * derivative ℚ G)) + C (-8) * (X ^ 3 * (X * derivative ℚ G)) +
      C 1 * G + C (-6) * (X ^ 1 * G) + C 12 * (X ^ 2 * G) + C (-8) * (X ^ 3 * G) =
      C 1 + C (-4) * X ^ 1 + C 6 * X ^ 2 + C (-4) * X ^ 3 := by
  have hSqD : 2 * S * derivative ℚ S = -8 + 16 * X := by
    have h := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at h
    linear_combination h
  have hRad : (1 - 8 * X + 8 * X ^ 2) * derivative ℚ S = (-4 + 8 * X) * S := by
    apply mul_left_cancel₀ two_ne
    linear_combination S * hSqD - 2 * derivative ℚ S * hSq
  have h1 : (2 * G - 1) * S = 2 - (2 * G - 1) := by linear_combination hG
  have hd : 2 * derivative ℚ G * (1 + S) + (2 * G - 1) * derivative ℚ S = 0 := by
    have h := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hG
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at h
    linear_combination h
  have h2 : 2 * (2 * derivative ℚ G) = -((2 * G - 1) ^ 2 * derivative ℚ S) := by
    linear_combination (2 * G - 1) * hd - 2 * derivative ℚ G * hG
  have h3 : (1 - 8 * X + 8 * X ^ 2) * (2 * derivative ℚ G) =
      (2 - 4 * X) * (2 * (2 * G - 1) - (2 * G - 1) ^ 2) := by
    apply mul_left_cancel₀ two_ne
    linear_combination (1 - 8 * X + 8 * X ^ 2) * h2 - (2 * G - 1) ^ 2 * hRad +
      (4 - 8 * X) * (2 * G - 1) * h1
  have hq : (2 * G - 1) - 1 - 2 * X * (1 - X) * (2 * G - 1) ^ 2 = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero two_ne two_ne)
    linear_combination ((2 * G - 1) * S + 2 - (2 * G - 1)) * h1 - (2 * G - 1) ^ 2 * hSq
  have key : (1 - 9 * X + 16 * X ^ 2 - 8 * X ^ 3) * (X * derivative ℚ G) +
      (1 - 6 * X + 12 * X ^ 2 - 8 * X ^ 3) * G = 1 - 4 * X + 6 * X ^ 2 - 4 * X ^ 3 := by
    apply mul_left_cancel₀ two_ne
    linear_combination X * (1 - X) * h3 + (1 - 2 * X) * hq
  simp only [map_neg, map_ofNat, map_one]
  linear_combination key

theorem OMA.solution : type_of% @OMA.S_oeis_a226316.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have h1 := congrArg (coeff (k + 4)) (generating_function_ode S G hSq hG)
  simp (disch := omega) only [map_add, coeff_C_mul, coeff_C, coeff_X_pow_mul', coeff_X_pow,
    if_pos, if_neg] at h1
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, coeff_X_derivative] at h1
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega]
  push_cast at h1 ⊢
  linear_combination h1
