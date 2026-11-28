import OMAStatements.S_oeis_a113956

open PowerSeries

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private theorem ne_zero_of_constantCoeff (F : ℚ⟦X⟧) (h : constantCoeff F ≠ 0) : F ≠ 0 := by
  intro hF
  apply h
  rw [hF, map_zero]

private theorem coeff_X_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff k (X * derivative ℚ G) = (k : ℚ) * coeff k G := by
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative, mul_comm]
    simp only [Nat.cast_add, Nat.cast_one]

private theorem generating_function_ode (S c G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X)
    (hS0 : coeff 0 S = 1)
    (hc : 2 * X * c = 1 - S)
    (hG : G * ((1 - 4 * X) * c * (S - X ^ 2 * c)) = S) :
    (C (1) * (X * derivative ℚ G) + C (0) * G) +
      X ^ 1 * (C (-10) * (X * derivative ℚ G) + C (-2) * G) +
      X ^ 2 * (C (27) * (X * derivative ℚ G) + C (8) * G) +
      X ^ 3 * (C (5) * (X * derivative ℚ G) + C (13) * G) +
      X ^ 4 * (C (-57) * (X * derivative ℚ G) + C (-40) * G) +
      X ^ 5 * (C (-42) * (X * derivative ℚ G) + C (-44) * G) +
      X ^ 6 * (C (-8) * (X * derivative ℚ G) + C (-12) * G) =
      C 1 * X ^ 1 - C 4 * X ^ 2 - C 2 * X ^ 3 - C 2 * X ^ 4 := by
  have h2 : (2 : ℚ⟦X⟧) ≠ 0 :=
    ne_zero_of_constantCoeff _ (by rw [map_ofNat]; norm_num)
  have h2X : (2 * X : ℚ⟦X⟧) ≠ 0 := mul_ne_zero h2 X_ne_zero
  have hS : S ≠ 0 := ne_zero_of_constantCoeff _ (by
    rw [← coeff_zero_eq_constantCoeff_apply, hS0]; norm_num)
  have hA : G * (1 - 4 * X) * ((1 + X) * S - (1 - 3 * X - 2 * X ^ 2)) = 2 * X * S := by
    apply mul_left_cancel₀ h2X
    linear_combination (4 * X ^ 2) * hG -
      (G * (1 - 4 * X) * (2 * X * S - X ^ 2 * (2 * X * c + 1 - S))) * hc +
      (G * (1 - 4 * X) * X * (2 + X)) * hSq
  have hB : G * ((1 - 3 * X - 4 * X ^ 2) - (1 - 3 * X - 2 * X ^ 2) * S) = 2 * X := by
    apply mul_left_cancel₀ hS
    linear_combination hA - (G * (1 - 3 * X - 2 * X ^ 2)) * hSq
  obtain ⟨H, hH⟩ : ∃ H : ℚ⟦X⟧, H = 2 * (1 - 7 * X + 8 * X ^ 2 + 15 * X ^ 3 + 4 * X ^ 4) * G - (1 - 3 * X - 4 * X ^ 2) := ⟨_, rfl⟩
  have hHS : H = (1 - 3 * X - 2 * X ^ 2) * S := by
    rw [hH]
    apply mul_left_cancel₀ h2X
    linear_combination ((1 - 3 * X - 4 * X ^ 2) + (1 - 3 * X - 2 * X ^ 2) * S) * hB +
      (G * (1 - 3 * X - 2 * X ^ 2) ^ 2) * hSq
  have hSS : S * derivative ℚ S = -2 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
    apply mul_left_cancel₀ h2
    linear_combination hd
  have hHSd : derivative ℚ H = (-3 - 4 * X) * S + (1 - 3 * X - 2 * X ^ 2) * derivative ℚ S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hHS
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
    linear_combination hd
  have hHODE : (1 - 3 * X - 2 * X ^ 2) * (1 - 4 * X) * derivative ℚ H =
      ((-3 - 4 * X) * (1 - 4 * X) - 2 * (1 - 3 * X - 2 * X ^ 2)) * H := by
    linear_combination ((1 - 3 * X - 2 * X ^ 2) * (1 - 4 * X)) * hHSd -
      ((-3 - 4 * X) * (1 - 4 * X) - 2 * (1 - 3 * X - 2 * X ^ 2)) * hHS +
      ((1 - 3 * X - 2 * X ^ 2) ^ 2 * S) * hSS - ((1 - 3 * X - 2 * X ^ 2) ^ 2 * derivative ℚ S) * hSq
  have hHd : derivative ℚ H = 2 * (1 - 7 * X + 8 * X ^ 2 + 15 * X ^ 3 + 4 * X ^ 4) * derivative ℚ G +
      2 * (-7 + 16 * X + 45 * X ^ 2 + 16 * X ^ 3) * G - (-3 - 8 * X) := by
    rw [hH]
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
    ring
  rw [hHd, hH] at hHODE
  have hF : (4 * X - 1 : ℚ⟦X⟧) ≠ 0 := ne_zero_of_constantCoeff _ (by simp)
  simp only [map_neg, map_zero, map_one, map_ofNat]
  apply mul_left_cancel₀ (mul_ne_zero h2 hF)
  linear_combination (-X) * hHODE

theorem OMA.solution : type_of% @OMA.S_oeis_a113956.main := by
  intro S c G hSq hS0 hc hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have hc := congrArg (coeff (k + 6)) (generating_function_ode S c G hSq hS0 hc hG)
  have h1 : ∀ F : ℚ⟦X⟧, coeff (k + 6) (X ^ 1 * F) = coeff (k + 5) F := by
    intro F
    rw [show k + 6 = k + 5 + 1 by omega, coeff_X_pow_mul]
  have h2 : ∀ F : ℚ⟦X⟧, coeff (k + 6) (X ^ 2 * F) = coeff (k + 4) F := by
    intro F
    rw [show k + 6 = k + 4 + 2 by omega, coeff_X_pow_mul]
  have h3 : ∀ F : ℚ⟦X⟧, coeff (k + 6) (X ^ 3 * F) = coeff (k + 3) F := by
    intro F
    rw [show k + 6 = k + 3 + 3 by omega, coeff_X_pow_mul]
  have h4 : ∀ F : ℚ⟦X⟧, coeff (k + 6) (X ^ 4 * F) = coeff (k + 2) F := by
    intro F
    rw [show k + 6 = k + 2 + 4 by omega, coeff_X_pow_mul]
  have h5 : ∀ F : ℚ⟦X⟧, coeff (k + 6) (X ^ 5 * F) = coeff (k + 1) F := by
    intro F
    rw [show k + 6 = k + 1 + 5 by omega, coeff_X_pow_mul]
  have h6 : ∀ F : ℚ⟦X⟧, coeff (k + 6) (X ^ 6 * F) = coeff k F := by
    intro F
    rw [coeff_X_pow_mul]
  have z0 : ¬ (k + 6 = 0) := by omega
  have z1 : ¬ (k + 6 = 1) := by omega
  have z2 : ¬ (k + 6 = 2) := by omega
  have z3 : ¬ (k + 6 = 3) := by omega
  have z4 : ¬ (k + 6 = 4) := by omega
  have hX : ∀ m : ℕ, m ≠ 1 → coeff m (X : ℚ⟦X⟧) = 0 := fun m hm => by
    rw [coeff_X, if_neg hm]
  have z1' : k + 6 ≠ 1 := by omega
  simp only [map_add, map_sub, coeff_C_mul, coeff_C, coeff_X_pow, h1, h2, h3, h4, h5, h6,
    hX _ z1', coeff_X_derivative, z0, z1, z2, z3, z4, if_false, mul_zero, add_zero, sub_zero, neg_zero] at hc
  simp only [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega, show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega, show k + 6 - 5 = k + 1 by omega, show k + 6 - 6 = k by omega]
  push_cast at hc ⊢
  linear_combination hc
