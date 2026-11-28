import OMAStatements.S_oeis_a114121

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

private theorem numeral_ne_zero (m : ℕ) [m.AtLeastTwo] (hm : 0 < m) :
    (OfNat.ofNat m : ℚ⟦X⟧) ≠ 0 := by
  rw [← map_ofNat C m]
  intro h
  have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
  simp only [constantCoeff_C, map_zero] at hc
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)) hc

private theorem generating_function_ode (S G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X)
    (hG : 2 * (1 - 4 * X) * G = S + (1 - 2 * X)) :
    (X * derivative ℚ G)
      - C 8 * (X ^ 1 * (X * derivative ℚ G))
      + C 16 * (X ^ 2 * (X * derivative ℚ G))
      - C 2 * (X ^ 1 * G)
      + C 8 * (X ^ 2 * G) = C 2 * X ^ 2 := by
  have hRadical : (1 - 4 * X) * derivative ℚ S = -2 * S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    apply mul_left_cancel₀ (numeral_ne_zero 2 (by decide))
    linear_combination S * hd - 2 * derivative ℚ S * hSq
  have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hG
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
  simp only [map_ofNat C 2, map_ofNat C 8, map_ofNat C 16]
  apply mul_left_cancel₀ (numeral_ne_zero 2 (by decide))
  linear_combination X * ((1 - 4 * X) * hd + hRadical + 2 * hG)

theorem OMA.solution : type_of% @OMA.S_oeis_a114121.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hCoeff := congrArg (coeff (k + 3)) (generating_function_ode S G hSq hG)
  simp (disch := omega) only [map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_X_pow, coeff_X_derivative,
    if_pos, if_neg, mul_zero] at hCoeff
  simp only [show k + 3 - 1 = k + 2 by omega,
    show k + 3 - 2 = k + 1 by omega] at hCoeff ⊢
  push_cast at hCoeff ⊢
  linear_combination hCoeff
