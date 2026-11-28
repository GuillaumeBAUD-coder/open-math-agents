import OMAStatements.S_oeis_a247173

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

private theorem first_order_ode (S G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4)
    (hG : G * ((2 * X ^ 2 + 2 * X) * S) = -S - 2 * X ^ 3 - 3 * X ^ 2 + 1) :
    (-2 * X ^ 6 - 9 * X ^ 5 + X ^ 4 + 14 * X ^ 3 - 5 * X + 1) * (X * derivative ℚ G) +
      (-2 * X ^ 6 - 6 * X ^ 5 - 3 * X ^ 4 + 8 * X ^ 3 - 6 * X + 1) * G =
      (-X ^ 4 - 4 * X ^ 3 + 10 * X ^ 2 - 4 * X + 1) := by
  have h2 : (2 : ℚ⟦X⟧) ≠ 0 :=
    ne_zero_of_constantCoeff _ (by rw [map_ofNat]; norm_num)
  obtain ⟨H, hH⟩ : ∃ H : ℚ⟦X⟧, H = (2 * X ^ 2 + 2 * X) * G + 1 := ⟨_, rfl⟩
  have hSH : S * H = (1 - 3 * X ^ 2 - 2 * X ^ 3) := by
    rw [hH]
    linear_combination hG
  have hSS : S * derivative ℚ S = (-2 - 2 * X + 6 * X ^ 2 + 2 * X ^ 3) := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
    apply mul_left_cancel₀ h2
    linear_combination hd
  have hSHd : derivative ℚ S * H + S * derivative ℚ H = (-6 * X - 6 * X ^ 2) := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSH
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
    linear_combination hd
  have hHODE : (1 - 3 * X ^ 2 - 2 * X ^ 3) * (1 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4) * derivative ℚ H =
      ((1 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4) * (-6 * X - 6 * X ^ 2) -
        (1 - 3 * X ^ 2 - 2 * X ^ 3) * (-2 - 2 * X + 6 * X ^ 2 + 2 * X ^ 3)) * H := by
    linear_combination ((1 - 3 * X ^ 2 - 2 * X ^ 3) * S) * hSHd -
      ((1 - 3 * X ^ 2 - 2 * X ^ 3) * H) * hSS +
      (H * (-6 * X - 6 * X ^ 2) - (1 - 3 * X ^ 2 - 2 * X ^ 3) * derivative ℚ H) * hSq -
      (S * (-6 * X - 6 * X ^ 2)) * hSH
  have hHd : derivative ℚ H = (2 * X ^ 2 + 2 * X) * derivative ℚ G + (4 * X + 2) * G := by
    rw [hH]
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
    ring
  rw [hHd, hH] at hHODE
  have hX1 : (X + 1 : ℚ⟦X⟧) ≠ 0 := ne_zero_of_constantCoeff _ (by simp)
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero h2 (X_ne_zero (R := ℚ))) (pow_ne_zero 2 hX1))
  linear_combination X * hHODE

private theorem second_order_ode (S G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4)
    (hG : G * ((2 * X ^ 2 + 2 * X) * S) = -S - 2 * X ^ 3 - 3 * X ^ 2 + 1) :
    (C (-3) * (X * derivative ℚ (X * derivative ℚ G)) + C (1) * (X * derivative ℚ G) + C (4) * G) +
      X ^ 1 * (C (9) * (X * derivative ℚ (X * derivative ℚ G)) + C (15) * (X * derivative ℚ G) + C (2) * G) +
      X ^ 2 * (C (18) * (X * derivative ℚ (X * derivative ℚ G)) + C (30) * (X * derivative ℚ G) + C (4) * G) +
      X ^ 3 * (C (-6) * (X * derivative ℚ (X * derivative ℚ G)) + C (-34) * (X * derivative ℚ G) + C (-32) * G) +
      X ^ 4 * (C (-15) * (X * derivative ℚ (X * derivative ℚ G)) + C (-67) * (X * derivative ℚ G) + C (-40) * G) +
      X ^ 5 * (C (-3) * (X * derivative ℚ (X * derivative ℚ G)) + C (-17) * (X * derivative ℚ G) + C (-14) * G) =
      C 4 + C 4 * X ^ 1 - C 12 * X ^ 2 - C 4 * X ^ 3 := by
  have hE := first_order_ode S G hSq hG
  have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hE
  simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
  have hF : (2 * X - 1 : ℚ⟦X⟧) ≠ 0 := ne_zero_of_constantCoeff _ (by simp)
  simp only [map_neg, map_one, map_ofNat, Derivation.leibniz, smul_eq_mul, derivative_X]
  apply mul_left_cancel₀ hF
  linear_combination (3 * X) * hd - 4 * hE

theorem OMA.solution : type_of% @OMA.S_oeis_a247173.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have hc := congrArg (coeff (k + 5)) (second_order_ode S G hSq hG)
  have h1 : ∀ F : ℚ⟦X⟧, coeff (k + 5) (X ^ 1 * F) = coeff (k + 4) F := by
    intro F
    rw [show k + 5 = k + 4 + 1 by omega, coeff_X_pow_mul]
  have h2 : ∀ F : ℚ⟦X⟧, coeff (k + 5) (X ^ 2 * F) = coeff (k + 3) F := by
    intro F
    rw [show k + 5 = k + 3 + 2 by omega, coeff_X_pow_mul]
  have h3 : ∀ F : ℚ⟦X⟧, coeff (k + 5) (X ^ 3 * F) = coeff (k + 2) F := by
    intro F
    rw [show k + 5 = k + 2 + 3 by omega, coeff_X_pow_mul]
  have h4 : ∀ F : ℚ⟦X⟧, coeff (k + 5) (X ^ 4 * F) = coeff (k + 1) F := by
    intro F
    rw [show k + 5 = k + 1 + 4 by omega, coeff_X_pow_mul]
  have h5 : ∀ F : ℚ⟦X⟧, coeff (k + 5) (X ^ 5 * F) = coeff k F := by
    intro F
    rw [coeff_X_pow_mul]
  have z0 : ¬ (k + 5 = 0) := by omega
  have z1 : ¬ (k + 5 = 1) := by omega
  have z2 : ¬ (k + 5 = 2) := by omega
  have z3 : ¬ (k + 5 = 3) := by omega
  have hX : ∀ m : ℕ, m ≠ 1 → coeff m (X : ℚ⟦X⟧) = 0 := fun m hm => by
    rw [coeff_X, if_neg hm]
  have z1' : k + 5 ≠ 1 := by omega
  simp only [map_add, map_sub, coeff_C_mul, coeff_C, coeff_X_pow, h1, h2, h3, h4, h5,
    hX _ z1', coeff_X_derivative, z0, z1, z2, z3, if_false, mul_zero, add_zero, sub_zero, neg_zero] at hc
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega, show k + 5 - 5 = k by omega]
  push_cast at hc ⊢
  linear_combination hc
