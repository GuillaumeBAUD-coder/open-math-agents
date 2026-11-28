import OMAStatements.S_oeis_a101596

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

private theorem generating_function_ode (S c G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 8 * X)
    (hc : 4 * X * c = 1 - S) (hG : G = c ^ 4) :
    X * derivative ℚ G - C 12 * (X * (X * derivative ℚ G)) +
      C 32 * (X ^ 2 * (X * derivative ℚ G)) + C 4 * G - C 40 * (X * G) +
      C 80 * (X ^ 2 * G) = C 4 := by
  have hEight : (8 * X : ℚ⟦X⟧) ≠ 0 := by
    refine mul_ne_zero ?_ X_ne_zero
    rw [← map_ofNat C 8]
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (8 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
    norm_num at hc
  have hS : S = 1 - 4 * X * c := by
    linear_combination hc
  have hQ : 2 * X * c ^ 2 - c + 1 = 0 := by
    apply mul_left_cancel₀ hEight
    rw [hS] at hSq
    linear_combination hSq
  have hD : 2 * c ^ 2 + 4 * X * c * derivative ℚ c - derivative ℚ c = 0 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hQ
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hd
    linear_combination hd
  have hE : X * (1 - 8 * X) * derivative ℚ c - 1 + (1 - 4 * X) * c = 0 := by
    linear_combination (-(X * (1 - 4 * X * c))) * hD -
      (1 + 4 * X * c + 8 * X ^ 2 * derivative ℚ c) * hQ
  have hGDerivative : derivative ℚ G = 4 * c ^ 3 * derivative ℚ c := by
    rw [hG]
    simp [Derivation.leibniz_pow, smul_eq_mul]
    ring
  rw [map_ofNat C 12, map_ofNat C 32, map_ofNat C 4, map_ofNat C 40, map_ofNat C 80,
    hGDerivative, hG]
  linear_combination (4 * c ^ 3 * (1 - 4 * X)) * hE -
    (4 * (c ^ 2 * (1 - 2 * X) + c + 1)) * hQ

theorem OMA.solution : type_of% @OMA.S_oeis_a101596.main := by
  intro S c G hSq _ hc hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have h := congrArg (coeff (k + 2)) (generating_function_ode S c G hSq hc hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_C, coeff_X_pow_mul,
    coeff_X_derivative, coeff_succ_X_mul, coeff_derivative, Nat.succ_ne_zero,
    if_false] at h
  simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  push_cast at h ⊢
  linear_combination h
