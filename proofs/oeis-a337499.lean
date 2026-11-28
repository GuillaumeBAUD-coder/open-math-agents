import OMAStatements.S_oeis_a337499

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

private theorem generating_function_ode (S G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : S * (1 + S) ^ 2 * G = (4 * X + 2) * S + 4 * X ^ 2 + 4 * X + 2) :
    (C (1) * (X * derivative ℚ G) + C (2) * G) +
      X ^ 1 * (C (1) * (X * derivative ℚ G) + C (1) * G) +
      X ^ 2 * (C (-5) * (X * derivative ℚ G) + C (-12) * G) +
      X ^ 3 * (C (-4) * (X * derivative ℚ G) + C (-8) * G) +
      X ^ 4 * (C (4) * (X * derivative ℚ G) + C (4) * G) =
      C 2 + C 7 * X ^ 1 + C 8 * X ^ 2 := by
  have h16 : (16 : ℚ⟦X⟧) ≠ 0 :=
    ne_zero_of_constantCoeff _ (by rw [map_ofNat]; norm_num)
  have hKey : X ^ 2 * S * G = 1 + X - X ^ 2 - (1 + X) * S := by
    apply mul_left_cancel₀ (mul_ne_zero h16 (pow_ne_zero 2 (X_ne_zero (R := ℚ))))
    linear_combination (1 - S) ^ 2 * hG +
      (S * G * (1 - S ^ 2 + 4 * X ^ 2) + (4 * X + 2) * S + 4 * X ^ 2 + 4 * X + 2 - 8 * X - 4) * hSq
  obtain ⟨H, hH⟩ : ∃ H : ℚ⟦X⟧, H = X ^ 2 * G + 1 + X := ⟨_, rfl⟩
  have hSH : S * H = 1 + X - X ^ 2 := by
    rw [hH]
    linear_combination hKey
  have hSS : S * derivative ℚ S = -4 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
    have h2 : (2 : ℚ⟦X⟧) ≠ 0 :=
      ne_zero_of_constantCoeff _ (by rw [map_ofNat]; norm_num)
    apply mul_left_cancel₀ h2
    linear_combination hd
  have hSHd : derivative ℚ S * H + S * derivative ℚ H = 1 - 2 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSH
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
    linear_combination hd
  have hHODE : (1 + X - X ^ 2) * (1 - 4 * X ^ 2) * derivative ℚ H =
      (1 + 2 * X + 4 * X ^ 3) * H := by
    linear_combination ((1 + X - X ^ 2) * S) * hSHd - ((1 + X - X ^ 2) * H) * hSS +
      (H * (1 - 2 * X) - (1 + X - X ^ 2) * derivative ℚ H) * hSq - (S * (1 - 2 * X)) * hSH
  have hHd : derivative ℚ H = X ^ 2 * derivative ℚ G + 2 * X * G + 1 := by
    rw [hH]
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
    ring
  rw [hHd, hH] at hHODE
  simp only [map_neg, map_one, map_ofNat]
  apply mul_left_cancel₀ (X_ne_zero (R := ℚ))
  linear_combination hHODE

theorem OMA.solution : type_of% @OMA.S_oeis_a337499.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hc := congrArg (coeff (k + 4)) (generating_function_ode S G hSq hG)
  have h1 : ∀ F : ℚ⟦X⟧, coeff (k + 4) (X ^ 1 * F) = coeff (k + 3) F := by
    intro F
    rw [show k + 4 = k + 3 + 1 by omega, coeff_X_pow_mul]
  have h2 : ∀ F : ℚ⟦X⟧, coeff (k + 4) (X ^ 2 * F) = coeff (k + 2) F := by
    intro F
    rw [show k + 4 = k + 2 + 2 by omega, coeff_X_pow_mul]
  have h3 : ∀ F : ℚ⟦X⟧, coeff (k + 4) (X ^ 3 * F) = coeff (k + 1) F := by
    intro F
    rw [show k + 4 = k + 1 + 3 by omega, coeff_X_pow_mul]
  have h4 : ∀ F : ℚ⟦X⟧, coeff (k + 4) (X ^ 4 * F) = coeff k F := by
    intro F
    rw [coeff_X_pow_mul]
  have z0 : ¬ (k + 4 = 0) := by omega
  have z1 : ¬ (k + 4 = 1) := by omega
  have z2 : ¬ (k + 4 = 2) := by omega
  have hX : ∀ m : ℕ, m ≠ 1 → coeff m (X : ℚ⟦X⟧) = 0 := fun m hm => by
    rw [coeff_X, if_neg hm]
  have z1' : k + 4 ≠ 1 := by omega
  simp only [map_add, map_sub, coeff_C_mul, coeff_C, coeff_X_pow, h1, h2, h3, h4,
    hX _ z1', coeff_X_derivative, z0, z1, z2, if_false, mul_zero, add_zero, sub_zero, neg_zero] at hc
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  push_cast at hc ⊢
  linear_combination hc
