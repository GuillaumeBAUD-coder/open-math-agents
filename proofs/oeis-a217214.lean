import OMAStatements.S_oeis_a217214

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

private theorem coeff_shift (f : ℚ⟦X⟧) (d k : ℕ) (h : k ≤ d) :
    coeff d (X ^ k * f) = coeff (d - k) f := by
  rw [coeff_X_pow_mul', if_pos h]

private theorem ne_zero_of_const (f : ℚ⟦X⟧) (h : constantCoeff f ≠ 0) : f ≠ 0 := by
  intro hf
  apply h
  rw [hf, map_zero]

private theorem first_order (S G F : ℚ⟦X⟧) (hSq : S ^ 2 = 1 - 4 * X)
    (hG : X * (1 - 4 * X) ^ 3 * G =
      (1 - 4 * X) ^ 3 * (1 - X - X ^ 2) - (1 - 11 * X + 39 * X ^ 2 - 40 * X ^ 3 - 22 * X ^ 4) * S)
    (hF : F = X * derivative ℚ G) :
    (1 - 11 * X + 39 * X ^ 2 - 40 * X ^ 3 - 22 * X ^ 4) * (1 - 4 * X) * F + (1 - 14 * X + 71 * X ^ 2 - 154 * X ^ 3 + 146 * X ^ 4 - 44 * X ^ 5) * G + (-(8 * X ^ 3) - 72 * X ^ 4 + 240 * X ^ 5 + 44 * X ^ 6) = 0 := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := ne_zero_of_const _ (by rw [map_ofNat]; norm_num)
  have hSd : 2 * S * derivative ℚ S = -4 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
    linear_combination hd
  have hODE : (1 - 4 * X) * derivative ℚ S = -(2 * S) := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSd - 2 * derivative ℚ S * hSq
  have hY : (1 - 4 * X) ^ 3 * (1 - X - X ^ 2 - X * G) = (1 - 11 * X + 39 * X ^ 2 - 40 * X ^ 3 - 22 * X ^ 4) * S := by
    linear_combination -hG
  have hYd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hY
  simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hYd
  have hw : ((1 - 4 * X) ^ 3 : ℚ⟦X⟧) ≠ 0 :=
    pow_ne_zero _ (ne_zero_of_const _ (by simp))
  apply mul_left_cancel₀ hw
  linear_combination (-((1 - 11 * X + 39 * X ^ 2 - 40 * X ^ 3 - 22 * X ^ 4) * (1 - 4 * X))) * hYd - (1 - 11 * X + 39 * X ^ 2 - 40 * X ^ 3 - 22 * X ^ 4) ^ 2 * hODE -
    (12 * (1 - 11 * X + 39 * X ^ 2 - 40 * X ^ 3 - 22 * X ^ 4) - (-1 + 12 * X - 42 * X ^ 2 - 8 * X ^ 3 + 132 * X ^ 4)) * hY + ((1 - 4 * X) ^ 3 * (1 - 11 * X + 39 * X ^ 2 - 40 * X ^ 3 - 22 * X ^ 4) * (1 - 4 * X)) * hF

private theorem key (S G F H : ℚ⟦X⟧) (hSq : S ^ 2 = 1 - 4 * X)
    (hG : X * (1 - 4 * X) ^ 3 * G =
      (1 - 4 * X) ^ 3 * (1 - X - X ^ 2) - (1 - 11 * X + 39 * X ^ 2 - 40 * X ^ 3 - 22 * X ^ 4) * S)
    (hF : F = X * derivative ℚ G) (hH : H = X * derivative ℚ F) :
    -C 423 * (X ^ 0 * H) -
      C 423 * (X ^ 1 * H) +
      C 17801 * (X ^ 2 * H) -
      C 37364 * (X ^ 3 * H) +
      C 1295 * (X ^ 0 * F) +
      C 3933 * (X ^ 1 * F) -
      C 13323 * (X ^ 2 * F) -
      C 10098 * (X ^ 3 * F) +
      C 1718 * (X ^ 0 * G) +
      C 6074 * (X ^ 1 * G) -
      C 22460 * (X ^ 2 * G) +
      C 14390 * (X ^ 3 * G) =
      C 3592 * X ^ 3 + C 33072 * X ^ 4 := by
  have hE := first_order S G F hSq hG hF
  have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hE
  simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
  have hQ : ((1 - 11 * X + 39 * X ^ 2 - 40 * X ^ 3 - 22 * X ^ 4) : ℚ⟦X⟧) ≠ 0 := ne_zero_of_const _ (by simp)
  simp only [map_ofNat]
  apply mul_left_cancel₀ hQ
  linear_combination (-423 - 2115 * X + 9341 * X ^ 2) * (X * hd) + (1718 + 5306 * X - 39510 * X ^ 2) * hE + (-423 - 2115 * X + 9341 * X ^ 2) * (1 - 14 * X + 71 * X ^ 2 - 154 * X ^ 3 + 146 * X ^ 4 - 44 * X ^ 5) * hF +
    (-423 - 2115 * X + 9341 * X ^ 2) * (1 - 11 * X + 39 * X ^ 2 - 40 * X ^ 3 - 22 * X ^ 4) * (1 - 4 * X) * hH

theorem OMA.solution : type_of% @OMA.S_oeis_a217214.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have hc := congrArg (coeff (k + 5)) (key S G _ _ hSq hG rfl rfl)
  simp (disch := omega) only [map_add, map_sub, map_neg, neg_mul, coeff_C_mul, coeff_shift,
    coeff_X_derivative, coeff_X_pow, if_neg, mul_zero, add_zero] at hc
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega, show k + 5 - 5 = k by omega, Nat.sub_zero] at hc ⊢
  push_cast at hc ⊢
  linear_combination hc
