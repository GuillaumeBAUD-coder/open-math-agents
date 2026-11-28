import OMAStatements.S_oeis_a278023

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

private theorem coeff_X_pow_mul_deriv3 (G : ℚ⟦X⟧) {k n : ℕ} (hk : k ≤ n) :
    coeff n (X ^ (k + 3) * derivative ℚ (derivative ℚ (derivative ℚ G))) =
      ((n : ℚ) - (k : ℚ)) * ((n : ℚ) - (k : ℚ) - 1) * ((n : ℚ) - (k : ℚ) - 2) * coeff (n - k) G := by
  by_cases h3 : k + 3 ≤ n
  · rw [coeff_X_pow_mul_of_le _ h3]
    have hsub1 : n - (k + 3) + 1 = n - (k + 2) := by omega
    have hsub2 : n - (k + 2) + 1 = n - (k + 1) := by omega
    have hsub3 : n - (k + 1) + 1 = n - k := by omega
    rw [coeff_derivative, hsub1, coeff_derivative, hsub2, coeff_derivative, hsub3]
    have hk2 : k + 2 ≤ n := by omega
    have hk1 : k + 1 ≤ n := by omega
    rw [Nat.cast_sub h3, Nat.cast_sub hk2, Nat.cast_sub hk1]
    push_cast
    ring
  · rw [coeff_X_pow_mul_of_lt _ (by omega)]
    have hcase : n = k ∨ n = k + 1 ∨ n = k + 2 := by omega
    rcases hcase with rfl | rfl | rfl <;> simp

private theorem generating_function_ode (S G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X)
    (hG : G * ((1 + 2 * X ^ 2 + S) * S) = 2 * X * (1 - X * S)) :
    C 3 * (X ^ 3 * derivative ℚ (derivative ℚ (derivative ℚ G))) -
      C 9 * (X ^ 4 * derivative ℚ (derivative ℚ (derivative ℚ G))) -
      C 12 * (X ^ 5 * derivative ℚ (derivative ℚ (derivative ℚ G))) +
      C 3 * (X ^ 6 * derivative ℚ (derivative ℚ (derivative ℚ G))) -
      C 12 * (X ^ 7 * derivative ℚ (derivative ℚ (derivative ℚ G))) -
      C 3 * (X ^ 2 * derivative ℚ (derivative ℚ G)) -
      C 12 * (X ^ 3 * derivative ℚ (derivative ℚ G)) -
      C 54 * (X ^ 4 * derivative ℚ (derivative ℚ G)) +
      C 24 * (X ^ 5 * derivative ℚ (derivative ℚ G)) -
      C 126 * (X ^ 6 * derivative ℚ (derivative ℚ G)) +
      C 2 * (X * derivative ℚ G) +
      C 6 * (X ^ 2 * derivative ℚ G) -
      C 26 * (X ^ 3 * derivative ℚ G) +
      C 38 * (X ^ 4 * derivative ℚ G) -
      C 314 * (X ^ 5 * derivative ℚ G) -
      C 4 * (X * G) +
      C 4 * (X ^ 2 * G) +
      C 6 * (X ^ 3 * G) -
      C 156 * (X ^ 4 * G) =
      C 2 * X - C 2 * X ^ 2 - C 6 * X ^ 3 + C 156 * X ^ 4 := by
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
  have hS' : (1 - 4 * X) * derivative ℚ S = -2 * S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    apply mul_left_cancel₀ hTwo
    linear_combination S * hd - 2 * derivative ℚ S * hSq
  have hG0 :
      2 * (1 - 4 * X) * (1 + X + X ^ 3) * G =
        (-1 + 3 * X + 4 * X ^ 2 - 2 * X ^ 3 + 8 * X ^ 4) + (1 + X - 2 * X ^ 2) * S := by
    apply mul_left_cancel₀ hTwo
    apply mul_left_cancel₀ hX
    linear_combination -((1 - 4 * X) - (1 + 2 * X ^ 2) * S) * hG +
      (-G * (1 + 2 * X ^ 2) * S - (4 * X + 4 * X ^ 2 + 4 * X ^ 4) * G - (2 * X ^ 2 + 4 * X ^ 4)) * hSq
  have hG1 :
      2 * (1 - 4 * X) ^ 2 * (1 + X + X ^ 3) ^ 2 * derivative ℚ G =
        (-3 * X ^ 2 + 22 * X ^ 3 - 32 * X ^ 4 - 32 * X ^ 5) +
          (2 + 9 * X ^ 2 + 16 * X ^ 3 + 12 * X ^ 4 - 12 * X ^ 5) * S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hG0
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination (1 - 4 * X) * (1 + X + X ^ 3) * hd -
      (-3 - 8 * X + 3 * X ^ 2 - 16 * X ^ 3) * hG0 +
      (1 + X + X ^ 3) * (1 + X - 2 * X ^ 2) * hS'
  have hG2 :
      2 * (1 - 4 * X) ^ 3 * (1 + X + X ^ 3) ^ 3 * derivative ℚ (derivative ℚ G) =
        (-6 * X + 66 * X ^ 2 - 218 * X ^ 3 + 132 * X ^ 4 + 150 * X ^ 5 + 632 * X ^ 6 -
            480 * X ^ 7 - 384 * X ^ 8) +
          (8 + 46 * X + 18 * X ^ 2 + 82 * X ^ 3 - 160 * X ^ 4 + 258 * X ^ 5 + 336 * X ^ 6 +
              180 * X ^ 7 - 120 * X ^ 8) * S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hG1
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination (1 - 4 * X) * (1 + X + X ^ 3) * hd -
      2 * (-3 - 8 * X + 3 * X ^ 2 - 16 * X ^ 3) * hG1 +
      (1 + X + X ^ 3) * (2 + 9 * X ^ 2 + 16 * X ^ 3 + 12 * X ^ 4 - 12 * X ^ 5) * hS'
  have hG3 :
      2 * (1 - 4 * X) ^ 4 * (1 + X + X ^ 3) ^ 4 * derivative ℚ (derivative ℚ (derivative ℚ G)) =
        (-6 + 96 * X - 576 * X ^ 2 + 1632 * X ^ 3 - 2988 * X ^ 4 + 7896 * X ^ 5 -
            16956 * X ^ 6 + 6312 * X ^ 7 + 9984 * X ^ 8 + 19200 * X ^ 9 - 9216 * X ^ 10 -
            6144 * X ^ 11) +
          (102 + 396 * X + 1020 * X ^ 2 - 552 * X ^ 3 + 4716 * X ^ 4 - 816 * X ^ 5 +
              1668 * X ^ 6 - 9984 * X ^ 7 + 6660 * X ^ 8 + 8232 * X ^ 9 + 3360 * X ^ 10 -
              1680 * X ^ 11) * S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hG2
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination (1 - 4 * X) * (1 + X + X ^ 3) * hd -
      3 * (-3 - 8 * X + 3 * X ^ 2 - 16 * X ^ 3) * hG2 +
      (1 + X + X ^ 3) * (8 + 46 * X + 18 * X ^ 2 + 82 * X ^ 3 - 160 * X ^ 4 + 258 * X ^ 5 +
        336 * X ^ 6 + 180 * X ^ 7 - 120 * X ^ 8) * hS'
  have hDenom : (2 * (1 - 4 * X) ^ 4 * (1 + X + X ^ 3) ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    have h2 : (2 : ℚ⟦X⟧) = C 2 := by rw [← map_ofNat C 2]
    rw [h2] at hc
    simp at hc
  rw [map_ofNat C 3, map_ofNat C 9, map_ofNat C 12, map_ofNat C 54, map_ofNat C 24,
    map_ofNat C 126, map_ofNat C 2, map_ofNat C 6, map_ofNat C 26, map_ofNat C 38,
    map_ofNat C 314, map_ofNat C 4, map_ofNat C 156]
  apply mul_left_cancel₀ hDenom
  linear_combination
    (3 * X ^ 3 - 9 * X ^ 4 - 12 * X ^ 5 + 3 * X ^ 6 - 12 * X ^ 7) * hG3 +
      (-3 * X ^ 2 - 12 * X ^ 3 - 54 * X ^ 4 + 24 * X ^ 5 - 126 * X ^ 6) * (1 - 4 * X) * (1 + X + X ^ 3) * hG2 +
      (2 * X + 6 * X ^ 2 - 26 * X ^ 3 + 38 * X ^ 4 - 314 * X ^ 5) * (1 - 4 * X) ^ 2 * (1 + X + X ^ 3) ^ 2 * hG1 +
      (-4 * X + 4 * X ^ 2 + 6 * X ^ 3 - 156 * X ^ 4) * (1 - 4 * X) ^ 3 * (1 + X + X ^ 3) ^ 3 * hG0

theorem OMA.solution : type_of% @OMA.S_oeis_a278023.main := by
  intro S G hSq _ hG n hn
  have hc := congrArg (coeff n) (generating_function_ode S G hSq hG)
  have hc2 : coeff n (C (2 : ℚ) * X - C (2 : ℚ) * X ^ 2 - C (6 : ℚ) * X ^ 3 + C (156 : ℚ) * X ^ 4) = 0 := by
    have h1 : n ≠ 1 := by omega
    have h2 : n ≠ 2 := by omega
    have h3 : n ≠ 3 := by omega
    have h4 : n ≠ 4 := by omega
    simp [coeff_X, h1, h2, h3, h4]
  rw [hc2] at hc
  simp only [map_add, map_sub, coeff_C_mul] at hc
  rw [coeff_X_pow_mul_deriv3 G (by omega),
    coeff_X_pow_mul_deriv3 G (by omega),
    coeff_X_pow_mul_deriv3 G (by omega),
    coeff_X_pow_mul_deriv3 G (by omega),
    coeff_X_pow_mul_deriv3 G (by omega),
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
    show (X : ℚ⟦X⟧) * G = X ^ 1 * G by ring,
    coeff_X_pow_mul_of_le G (by omega),
    coeff_X_pow_mul_of_le G (by omega),
    coeff_X_pow_mul_of_le G (by omega),
    coeff_X_pow_mul_of_le G (by omega)] at hc
  simp only [Nat.cast_zero, sub_zero] at hc
  push_cast at hc
  linear_combination hc
