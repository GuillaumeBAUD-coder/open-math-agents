import OMAStatements.S_oeis_a105695

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

private theorem series_two_ne_zero : (2 : ℚ⟦X⟧) ≠ 0 := by
  rw [← map_ofNat C 2]
  intro h
  have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
  change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
  norm_num at hc

private theorem generating_function_ode (T G : ℚ⟦X⟧)
    (hSq : T ^ 2 * (1 + X) = 1 - 3 * X)
    (hG : 2 * X * G = (1 - X) * (1 + X) * (1 - T)) :
    (X * derivative ℚ G - C 3 * (X * (X * derivative ℚ G)) -
      X ^ 2 * (X * derivative ℚ G) + C 3 * (X ^ 3 * (X * derivative ℚ G))) +
    (G - X * G - X ^ 2 * G - C 3 * (X ^ 3 * G)) =
    1 - X - X ^ 2 + X ^ 3 := by
  have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
  have hT : (1 + X) * (1 - 3 * X) * derivative ℚ T = -2 * T := by
    apply mul_left_cancel₀ series_two_ne_zero
    linear_combination (1 + X) * T * hd - (2 * (1 + X) * derivative ℚ T + T) * hSq
  have hg' := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hG
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hg'
  rw [map_ofNat C 3]
  apply mul_left_cancel₀ series_two_ne_zero
  linear_combination (1 - X) * (1 + X) * (1 - 3 * X) * hg' -
    (1 - X)^2 * (1 + X) * hT + (2 * (1 - X) + 2 * X * (1 - 3 * X)) * hG

theorem OMA.solution : type_of% @OMA.S_oeis_a105695.main := by
  intro T G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hc := congrArg (coeff (k + 4)) (generating_function_ode T G hSq hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_succ_X_mul,
    if_pos (show 2 ≤ k + 4 by omega), if_pos (show 3 ≤ k + 4 by omega),
    coeff_one, coeff_X, coeff_X_pow, if_neg (show k + 4 ≠ 0 by omega),
    if_neg (show k + 4 ≠ 1 by omega), if_neg (show k + 4 ≠ 2 by omega),
    if_neg (show k + 4 ≠ 3 by omega)] at hc
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega] at hc ⊢
  simp only [coeff_X_derivative, coeff_derivative] at hc
  push_cast at hc ⊢
  linear_combination hc
