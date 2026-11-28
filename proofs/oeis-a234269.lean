import OMAStatements.S_oeis_a234269

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

private theorem first_order (S G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X ^ 2 - 4 * X ^ 3)
    (hG : G * (2 * X * S) = 1 - 2 * X ^ 2 - S) :
    (1 - 6 * X ^ 2 - 4 * X ^ 3 + 8 * X ^ 4 + 8 * X ^ 5) * (X * derivative ℚ G) +
      (1 - 6 * X ^ 2 - 10 * X ^ 3 + 4 * X ^ 5) * G = 3 * X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4 := by
  have e1 : S * (1 + 2 * X * G) = 1 - 2 * X ^ 2 := by linear_combination hG
  have d1 : derivative ℚ S * (1 + 2 * X * G) + S * (2 * G + 2 * X * derivative ℚ G) =
      -4 * X := by
    have h := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) e1
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at h
    linear_combination h
  have dsq : S * derivative ℚ S = -4 * X - 6 * X ^ 2 := by
    apply mul_left_cancel₀ two_ne
    have h := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at h
    linear_combination h
  apply mul_left_cancel₀ two_ne
  linear_combination (1 - 2 * X ^ 2) * S * d1 - (1 - 2 * X ^ 2) * (1 + 2 * X * G) * dsq -
    (1 - 2 * X ^ 2) * (2 * G + 2 * X * derivative ℚ G) * hSq - S * (-4 * X) * e1 +
    (1 + 2 * X * G) * (-4 * X) * hSq

private theorem generating_function_ode (S G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X ^ 2 - 4 * X ^ 3)
    (hG : G * (2 * X * S) = 1 - 2 * X ^ 2 - S) :
    C (-2) * (X * derivative ℚ (X * derivative ℚ G)) +
      C (-2) * (X ^ 1 * (X * derivative ℚ (X * derivative ℚ G))) +
      C 8 * (X ^ 2 * (X * derivative ℚ (X * derivative ℚ G))) +
      C 16 * (X ^ 3 * (X * derivative ℚ (X * derivative ℚ G))) +
      C 8 * (X ^ 4 * (X * derivative ℚ (X * derivative ℚ G))) +
      C 3 * (X * derivative ℚ G) + C 4 * (X ^ 1 * (X * derivative ℚ G)) +
      C 12 * (X ^ 2 * (X * derivative ℚ G)) + C 32 * (X ^ 3 * (X * derivative ℚ G)) +
      C 20 * (X ^ 4 * (X * derivative ℚ G)) +
      C 5 * G + C 6 * (X ^ 1 * G) + C 4 * (X ^ 2 * G) + C 10 * (X ^ 3 * G) +
      C 8 * (X ^ 4 * G) =
      C 3 * X ^ 2 + C 2 * X ^ 3 := by
  have h1 := first_order S G hSq hG
  have hW : (1 - 2 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    simp at hc
  have h2 : (-12 * X - 12 * X ^ 2 + 32 * X ^ 3 + 40 * X ^ 4) * (X * derivative ℚ G) +
      (1 - 6 * X ^ 2 - 4 * X ^ 3 + 8 * X ^ 4 + 8 * X ^ 5) *
        derivative ℚ (X * derivative ℚ G) +
      (-12 * X - 30 * X ^ 2 + 20 * X ^ 4) * G +
      (1 - 6 * X ^ 2 - 10 * X ^ 3 + 4 * X ^ 5) * derivative ℚ G =
      6 * X + 12 * X ^ 2 + 8 * X ^ 3 := by
    have h := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) h1
    generalize hD : X * derivative ℚ G = D at h ⊢
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at h
    linear_combination h
  simp only [map_neg, map_ofNat]
  apply mul_left_cancel₀ hW
  linear_combination (-2 * (1 + X) * X) * h2 + (5 + 6 * X) * h1

theorem OMA.solution : type_of% @OMA.S_oeis_a234269.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have h1 := congrArg (coeff (k + 4)) (generating_function_ode S G hSq hG)
  simp (disch := omega) only [map_add, coeff_C_mul, coeff_X_pow, coeff_X_pow_mul',
    if_pos, if_neg] at h1
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega, coeff_X_derivative] at h1
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  push_cast at h1 ⊢
  linear_combination h1
