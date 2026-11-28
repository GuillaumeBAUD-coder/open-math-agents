import OMAStatements.S_oeis_a174107

open PowerSeries

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private noncomputable def θ (f : ℚ⟦X⟧) : ℚ⟦X⟧ := X * derivative ℚ f

private theorem coeff_θ (f : ℚ⟦X⟧) (m : ℕ) :
    coeff m (θ f) = (m : ℚ) * coeff m f := by
  cases m with
  | zero => simp [θ]
  | succ m =>
    rw [θ, coeff_succ_X_mul, coeff_derivative, mul_comm]
    simp only [Nat.cast_add, Nat.cast_one]

private theorem coeff_shift (n k : ℕ) (h : k ≤ n) (f : ℚ⟦X⟧) :
    coeff n (X ^ k * f) = coeff (n - k) f := by
  conv_lhs => rw [← Nat.sub_add_cancel h]
  exact coeff_X_pow_mul f k (n - k)

private theorem coeff_ofNat_mul (k : ℕ) [k.AtLeastTwo] (f : ℚ⟦X⟧) (m : ℕ) :
    coeff m ((no_index (OfNat.ofNat k : ℚ⟦X⟧)) * f) =
      (no_index (OfNat.ofNat k : ℚ)) * coeff m f := by
  rw [← map_ofNat C k, coeff_C_mul]

private theorem generating_function_ode (T G : ℚ⟦X⟧)
    (hSq : T ^ 2 * (1 - X + X ^ 2) = 1 - 5 * X + X ^ 2)
    (hT0 : coeff 0 T = 1)
    (hG : 2 * X * G = 1 - T) :
    (1 - 6 * X + 7 * X ^ 2 - 6 * X ^ 3 + X ^ 4) * θ G +
      (1 - 4 * X + 7 * X ^ 2 - 8 * X ^ 3 + X ^ 4) * G = 1 - X ^ 2 := by
  have h2_ne : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    intro h
    have := congrArg (coeff 0) h
    simp only [coeff_C, ↓reduceIte, map_zero] at this
    norm_num at this
  have hX_ne : (X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (coeff 1) h
    simp at this
  have hT_ne : T ≠ 0 := by
    intro h
    rw [h, map_zero] at hT0
    norm_num at hT0
  have hθT : θ T = -2 * X * (G + θ G) := by
    have hd := congrArg (derivative ℚ) hG
    simp only [map_sub, derivative_one, Derivation.leibniz, derivative_X,
      derivative_numeral, smul_eq_mul] at hd
    dsimp only [θ]
    linear_combination X * hd
  have hT_ode : T * (1 - X + X ^ 2) ^ 2 * (G + θ G) = 1 - X ^ 2 := by
    have hd := congrArg (derivative ℚ) hSq
    simp only [map_add, map_sub, derivative_one, derivative_X, derivative_numeral,
      Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul,
      Nat.cast_ofNat] at hd
    have hXθ : 2 * T * (1 - X + X ^ 2) ^ 2 * θ T = -4 * X * (1 - X ^ 2) := by
      have h1 := congrArg (fun f : ℚ⟦X⟧ => X * (1 - X + X ^ 2) * f) hd
      dsimp only [θ]
      linear_combination h1 - X * (-1 + 2 * X) * hSq
    rw [hθT] at hXθ
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero h2_ne h2_ne) hX_ne)
    linear_combination -hXθ
  linear_combination (1 - X ^ 2) * hG + T * hT_ode - (1 - X + X ^ 2) * (G + θ G) * hSq

theorem OMA.solution : type_of% @OMA.S_oeis_a174107.main := by
  intro T G hSq hT0 hG n hn
  have hcoef := congrArg (coeff n) (generating_function_ode T G hSq hT0 hG)
  have hn0 : n ≠ 0 := by omega
  have hn2 : n ≠ 2 := by omega
  have hs1 := coeff_shift n 1 (by omega)
  have hs2 := coeff_shift n 2 (by omega)
  have hs3 := coeff_shift n 3 (by omega)
  have hs4 := coeff_shift n 4 (by omega)
  have hc1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hc2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat]
  have hc3 : ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_ofNat]
  have hc4 : ((n - 4 : ℕ) : ℚ) = (n : ℚ) - 4 := by
    rw [Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_ofNat]
  have hL : (1 - 6 * X + 7 * X ^ 2 - 6 * X ^ 3 + X ^ 4) * θ G +
      (1 - 4 * X + 7 * X ^ 2 - 8 * X ^ 3 + X ^ 4) * G =
      (θ G - 6 * (X ^ 1 * θ G) + 7 * (X ^ 2 * θ G) - 6 * (X ^ 3 * θ G) + X ^ 4 * θ G) +
      (G - 4 * (X ^ 1 * G) + 7 * (X ^ 2 * G) - 8 * (X ^ 3 * G) + X ^ 4 * G) := by ring
  rw [hL] at hcoef
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_one, coeff_X_pow, hn0, hn2,
    ↓reduceIte, hs1, hs2, hs3, hs4, coeff_θ, hc1, hc2, hc3, hc4] at hcoef
  linear_combination hcoef
