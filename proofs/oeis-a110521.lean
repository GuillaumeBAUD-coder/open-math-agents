import OMAStatements.S_oeis_a110521

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

private theorem generating_function_ode (S c G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 12 * X)
    (hc : 6 * X * c = 1 - S)
    (hG : G * (1 - (X + X ^ 2) * c) = 1) :
    C 2 * (X * derivative ℚ G)
      - C 22 * (X ^ 1 * (X * derivative ℚ G))
      - C 22 * (X ^ 2 * (X * derivative ℚ G))
      - C 21 * (X ^ 3 * (X * derivative ℚ G))
     
      - C 35 * (X ^ 4 * (X * derivative ℚ G))
      - C 12 * (X ^ 5 * (X * derivative ℚ G))
      + C 10 * (X ^ 1 * G)
      + C 40 * (X ^ 2 * G)
      - C 31 * (X ^ 3 * G)
      - C 40 * (X ^ 4 * G)
      - C 18 * (X ^ 5 * G) = C 12 * X
      + C 48 * X ^ 2
      - C 3 * X ^ 3 := by
  have hRadical : (1 - 12 * X) * derivative ℚ S = (-6) * S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    apply mul_left_cancel₀ (numeral_ne_zero 2 (by decide))
    linear_combination S * hd - 2 * derivative ℚ S * hSq
  have hDenom : G * ((5 - X) + (1 + X) * S) = 6 := by
    linear_combination 6 * hG + G * (1 + X) * hc
  -- Multiply the denominator by its conjugate to eliminate the square.
  have hConjugate : (24 + 24 * X ^ 2 + 12 * X ^ 3) * G = 6 * ((5 - X) - (1 + X) * S) := by
    linear_combination ((5 - X) - (1 + X) * S) * hDenom + (1 + X) ^ 2 * G * hSq
  have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hConjugate
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
  simp only [map_ofNat C 2, map_ofNat C 3, map_ofNat C 10, map_ofNat C 12, map_ofNat C 18,
    map_ofNat C 21, map_ofNat C 22, map_ofNat C 31, map_ofNat C 35, map_ofNat C 40, map_ofNat C 48]
  apply mul_left_cancel₀ (numeral_ne_zero 12 (by decide))
  linear_combination X * ((1 - 11 * X - 12 * X ^ 2) * hd - (-5 - 18 * X) * hConjugate -
    6 * (1 + X) ^ 2 * hRadical)

theorem OMA.solution : type_of% @OMA.S_oeis_a110521.main := by
  intro S c G hSq _ hc hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have hCoeff := congrArg (coeff (k + 5)) (generating_function_ode S c G hSq hc hG)
  simp (disch := omega) only [map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_X_pow, coeff_X_derivative,
    coeff_X, if_pos, if_neg, mul_zero, add_zero, sub_zero] at hCoeff
  simp only [show k + 5 - 1 = k + 4 by omega,
    show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega,
    show k + 5 - 4 = k + 1 by omega,
    show k + 5 - 5 = k by omega] at hCoeff ⊢
  push_cast at hCoeff ⊢
  linear_combination hCoeff
