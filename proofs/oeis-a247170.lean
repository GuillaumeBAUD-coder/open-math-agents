import OMAStatements.S_oeis_a247170

open PowerSeries

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

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

private theorem coeff_X_pow_mul_deriv2 (G : ℚ⟦X⟧) {k n : ℕ} (hk : k ≤ n) :
    coeff n (X ^ (k + 2) * derivative ℚ (derivative ℚ G)) =
      ((n : ℚ) - (k : ℚ)) * ((n : ℚ) - (k : ℚ) - 1) * coeff (n - k) G := by
  by_cases h2 : k + 2 ≤ n
  · rw [coeff_X_pow_mul_of_le _ h2]
    have hsub1 : n - (k + 2) + 1 = n - (k + 1) := by omega
    have hsub2 : n - (k + 1) + 1 = n - k := by omega
    rw [coeff_derivative, hsub1, coeff_derivative, hsub2]
    have hk1 : k + 1 ≤ n := by omega
    rw [Nat.cast_sub h2, Nat.cast_sub hk1]
    push_cast
    ring
  · rw [coeff_X_pow_mul_of_lt _ (by omega)]
    have hcase : n = k ∨ n = k + 1 := by omega
    rcases hcase with rfl | rfl <;> simp

private theorem generating_function_ode (S G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (2 * X * S) = X ^ 3 + 3 * X - 3 * X * S) :
    C 2 * (X ^ 2 * derivative ℚ (derivative ℚ G)) +
      C 2 * (X ^ 3 * derivative ℚ (derivative ℚ G)) -
      C 4 * (X ^ 4 * derivative ℚ (derivative ℚ G)) -
      C 12 * (X ^ 5 * derivative ℚ (derivative ℚ G)) -
      C 6 * (X ^ 6 * derivative ℚ (derivative ℚ G)) +
      C 2 * (X ^ 7 * derivative ℚ (derivative ℚ G)) -
      C 5 * (X * derivative ℚ G) -
      C 5 * (X ^ 2 * derivative ℚ G) -
      C 2 * (X ^ 3 * derivative ℚ G) -
      C 18 * (X ^ 4 * derivative ℚ G) -
      C 9 * (X ^ 5 * derivative ℚ G) +
      C 7 * (X ^ 6 * derivative ℚ G) +
      C 8 * (X ^ 2 * G) +
      C 14 * (X ^ 3 * G) +
      C 6 * (X ^ 4 * G) =
      -(C 12 * X ^ 2 + C 21 * X ^ 3 + C 9 * X ^ 4) := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
    norm_num at hc
  have hX : (X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (coeff 1) h
    simp at hc
  have hSG : S * (2 * G + 3) = X ^ 2 + 3 := by
    apply mul_left_cancel₀ hX
    linear_combination hG
  have hSqDeriv : (1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4) * derivative ℚ S =
      (-2 * X - 6 * X ^ 2 + 2 * X ^ 3) * S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    apply mul_left_cancel₀ hTwo
    linear_combination S * hd - 2 * derivative ℚ S * hSq
  have hSGDeriv : derivative ℚ S * (2 * G + 3) + 2 * S * derivative ℚ G = 2 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSG
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hFirstOrder :
      (1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4) * (X ^ 2 + 3) * derivative ℚ G +
        (-4 * X - 9 * X ^ 2 + 4 * X ^ 3 + X ^ 4) * (2 * G + 3) = 0 := by
    apply mul_left_cancel₀ hTwo
    linear_combination (2 * G + 3) * (1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4) * hSGDeriv -
      (2 * G + 3) ^ 2 * hSqDeriv -
      (-2 * X - 6 * X ^ 2 + 2 * X ^ 3) * (2 * G + 3) * hSG -
      2 * (1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4) * derivative ℚ G * hSG
  have hFirstOrderDeriv := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hFirstOrder
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hFirstOrderDeriv
  have hQ : (X ^ 2 + 3 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    have h3 : (3 : ℚ⟦X⟧) = C 3 := by rw [← map_ofNat C 3]
    rw [h3] at hc
    simp at hc
  rw [map_ofNat C 2, map_ofNat C 4, map_ofNat C 12, map_ofNat C 6, map_ofNat C 5,
    map_ofNat C 18, map_ofNat C 9, map_ofNat C 7, map_ofNat C 8, map_ofNat C 14,
    map_ofNat C 21]
  apply mul_left_cancel₀ hQ
  linear_combination (2 * X ^ 2 + 2 * X ^ 3) * hFirstOrderDeriv +
    (-5 * X - 5 * X ^ 2) * hFirstOrder

theorem OMA.solution : type_of% @OMA.S_oeis_a247170.main := by
  intro S G hSq _ hG n hn
  have hc := congrArg (coeff n) (generating_function_ode S G hSq hG)
  have hc2 : coeff n (-(C (12 : ℚ) * X ^ 2 + C (21 : ℚ) * X ^ 3 + C (9 : ℚ) * X ^ 4)) = 0 := by
    have h2 : n ≠ 2 := by omega
    have h3 : n ≠ 3 := by omega
    have h4 : n ≠ 4 := by omega
    simp [h2, h3, h4]
  rw [hc2] at hc
  simp only [map_add, map_sub, coeff_C_mul] at hc
  rw [coeff_X_pow_mul_deriv2 G (by omega),
    coeff_X_pow_mul_deriv2 G (by omega),
    coeff_X_pow_mul_deriv2 G (by omega),
    coeff_X_pow_mul_deriv2 G (by omega),
    coeff_X_pow_mul_deriv2 G (by omega),
    coeff_X_pow_mul_deriv2 G (by omega),
    show (X : ℚ⟦X⟧) * derivative ℚ G = X ^ (0 + 1) * derivative ℚ G by ring,
    coeff_X_pow_mul_deriv G (by omega),
    coeff_X_pow_mul_deriv G (by omega),
    coeff_X_pow_mul_deriv G (by omega),
    coeff_X_pow_mul_deriv G (by omega),
    coeff_X_pow_mul_deriv G (by omega),
    coeff_X_pow_mul_deriv G (by omega),
    coeff_X_pow_mul_of_le G (by omega),
    coeff_X_pow_mul_of_le G (by omega),
    coeff_X_pow_mul_of_le G (by omega)] at hc
  simp only [Nat.cast_zero, sub_zero] at hc
  push_cast at hc
  linear_combination hc
