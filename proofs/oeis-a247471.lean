import OMAStatements.S_oeis_a247471

open PowerSeries

private theorem coeff_X_pow_mul_of_le (f : ℚ⟦X⟧) {k n : ℕ} (hk : k ≤ n) :
    coeff n (X ^ k * f) = coeff (n - k) f := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + k := ⟨n - k, by omega⟩
  rw [coeff_X_pow_mul, Nat.add_sub_cancel]

private theorem coeff_X_pow_mul_of_lt (f : ℚ⟦X⟧) {k n : ℕ} (hk : n < k) :
    coeff n (X ^ k * f) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = n + (m + 1) := ⟨k - n - 1, by omega⟩
  have h : coeff n (X ^ (n + (m + 1)) * f) = coeff (0 + n) (X ^ n * (X ^ (m + 1) * f)) := by
    rw [zero_add, pow_add, mul_assoc]
  rw [h, coeff_X_pow_mul, pow_add, pow_one, mul_assoc]
  simp

private theorem coeff_X_pow_mul_deriv (G : ℚ⟦X⟧) {k n : ℕ} (hk : k ≤ n) :
    coeff n (X ^ (k + 1) * derivative ℚ G) = ((n : ℚ) - (k : ℚ)) * coeff (n - k) G := by
  rcases eq_or_lt_of_le hk with rfl | hlt
  · rw [coeff_X_pow_mul_of_lt _ (by omega), sub_self, zero_mul]
  · rw [coeff_X_pow_mul_of_le _ (by omega)]
    have hsub : n - (k + 1) + 1 = n - k := by omega
    rw [coeff_derivative, hsub]
    have hc : ((n - (k + 1) : ℕ) : ℚ) + 1 = (n : ℚ) - (k : ℚ) := by
      have : (k : ℚ) + 1 ≤ (n : ℚ) := by exact_mod_cast hlt
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hc, mul_comm]

private theorem generating_function_ode (T G : ℚ⟦X⟧)
    (hT : T = 1 + X * T + X ^ 2 * T + X ^ 3 * T ^ 2)
    (hG : G = X ^ 3 * (1 - X - X ^ 2) * T ^ 2) :
    (X * derivative ℚ G) -
      C 3 * (X ^ 2 * derivative ℚ G) +
      (X ^ 4 * derivative ℚ G) +
      C 4 * (X ^ 5 * derivative ℚ G) +
      (X ^ 6 * derivative ℚ G) -
      (X ^ 7 * derivative ℚ G) +
      C 3 * G -
      C 6 * (X * G) -
      C 6 * (X ^ 3 * G) -
      C 2 * (X ^ 4 * G) -
      C 4 * (X ^ 5 * G) +
      C 3 * (X ^ 6 * G) =
      C 6 * X ^ 3 - C 8 * X ^ 4 - C 2 * X ^ 5 - C 2 * X ^ 7 := by
  have hAlg : X ^ 3 * (G + (1 - X - X ^ 2)) ^ 2 - (1 - X - X ^ 2) ^ 3 * G = 0 := by
    have hGT : G + (1 - X - X ^ 2) = (1 - X - X ^ 2) ^ 2 * T := by
      linear_combination hG - (1 - X - X ^ 2) * hT
    linear_combination (G + (1 - X - X ^ 2) + (1 - X - X ^ 2) ^ 2 * T) * X ^ 3 * hGT -
      (1 - X - X ^ 2) ^ 3 * hG
  have hAlgDeriv :
      ((1 - X - X ^ 2) ^ 3 - 2 * X ^ 3 * (G + (1 - X - X ^ 2))) * derivative ℚ G =
        3 * X ^ 2 * (G + (1 - X - X ^ 2)) ^ 2 +
          2 * X ^ 3 * (G + (1 - X - X ^ 2)) * (-1 - 2 * X) -
          3 * (1 - X - X ^ 2) ^ 2 * (-1 - 2 * X) * G := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hAlg
    simp [Derivation.leibniz, smul_eq_mul] at hd
    linear_combination -hd
  have hDenom : ((1 - X - X ^ 2) ^ 3 - 2 * X ^ 3 * (G + (1 - X - X ^ 2)) : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    simp at hc
  rw [map_ofNat C 3, map_ofNat C 4, map_ofNat C 6, map_ofNat C 2, map_ofNat C 8]
  apply mul_left_cancel₀ hDenom
  linear_combination
    (X - 3 * X ^ 2 + X ^ 4 + 4 * X ^ 5 + X ^ 6 - X ^ 7) * hAlgDeriv +
      (-3 + 3 * X + 15 * X ^ 3 + 16 * X ^ 4 + 11 * X ^ 5 - 9 * X ^ 6) * hAlg

theorem OMA.solution : type_of% @OMA.S_oeis_a247471.main := by
  intro T G hT hG n hn
  have hc := congrArg (coeff n) (generating_function_ode T G hT hG)
  have hc2 : coeff n (C (6 : ℚ) * X ^ 3 - C (8 : ℚ) * X ^ 4 - C (2 : ℚ) * X ^ 5 - C (2 : ℚ) * X ^ 7) = 0 := by
    have h3 : n ≠ 3 := by omega
    have h4 : n ≠ 4 := by omega
    have h5 : n ≠ 5 := by omega
    have h7 : n ≠ 7 := by omega
    simp [h3, h4, h5, h7]
  rw [hc2] at hc
  simp only [map_add, map_sub, coeff_C_mul] at hc
  rw [show (X : ℚ⟦X⟧) * derivative ℚ G = X ^ (0 + 1) * derivative ℚ G by ring,
    coeff_X_pow_mul_deriv G (by omega),
    coeff_X_pow_mul_deriv G (by omega),
    coeff_X_pow_mul_deriv G (by omega),
    coeff_X_pow_mul_deriv G (by omega),
    coeff_X_pow_mul_deriv G (by omega),
    coeff_X_pow_mul_deriv G (by omega),
    show (X : ℚ⟦X⟧) * G = X ^ 1 * G by ring,
    coeff_X_pow_mul_of_le G (by omega),
    coeff_X_pow_mul_of_le G (by omega),
    coeff_X_pow_mul_of_le G (by omega),
    coeff_X_pow_mul_of_le G (by omega),
    coeff_X_pow_mul_of_le G (by omega)] at hc
  simp only [Nat.cast_zero, sub_zero] at hc
  push_cast at hc
  linear_combination hc
