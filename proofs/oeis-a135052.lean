import OMAStatements.S_oeis_a135052

open PowerSeries

private lemma derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m, derivative_C]

private lemma coeff_numeral_mul (m n : ℕ) [m.AtLeastTwo] (F : ℚ⟦X⟧) :
    coeff n (no_index (OfNat.ofNat m : ℚ⟦X⟧) * F) = (OfNat.ofNat m : ℚ) * coeff n F := by
  rw [← map_ofNat C m, coeff_C_mul]

private noncomputable def euler (F : ℚ⟦X⟧) : ℚ⟦X⟧ := X * derivative ℚ F

private lemma coeff_euler (F : ℚ⟦X⟧) (n : ℕ) :
    coeff n (euler F) = coeff n F * (n : ℚ) := by
  cases n with
  | zero => simp [euler]
  | succ n => rw [euler, coeff_succ_X_mul, coeff_derivative, Nat.cast_succ]

private lemma coeff_shift_one (F : ℚ⟦X⟧) (n : ℕ) (hn : 1 ≤ n) :
    coeff n (X * F) = coeff (n - 1) F := by
  rw [← pow_one (X : ℚ⟦X⟧), coeff_X_pow_mul', if_pos hn]

theorem OMA.solution : type_of% @OMA.S_oeis_a135052.main := by
  intro S G hS _ hG n hn
  let R : ℚ⟦X⟧ := 1 - 4 * X + 8 * X ^ 3 - 4 * X ^ 4
  let Rp : ℚ⟦X⟧ := -4 + 24 * X ^ 2 - 16 * X ^ 3
  have hdS := congrArg (derivative ℚ) hS
  simp [Derivation.leibniz, smul_eq_mul, derivative_numeral] at hdS
  have hdG := congrArg (derivative ℚ) hG
  simp [Derivation.leibniz, smul_eq_mul, derivative_numeral] at hdG
  have hEuler :
      4 * (X * euler G) - 20 * (X ^ 2 * euler G) + 16 * (X ^ 3 * euler G) +
        32 * (X ^ 4 * euler G) - 48 * (X ^ 5 * euler G) + 16 * (X ^ 6 * euler G) +
        8 * (X * G) - 36 * (X ^ 2 * G) + 40 * (X ^ 3 * G) + 16 * (X ^ 4 * G) -
        48 * (X ^ 5 * G) + 16 * (X ^ 6 * G) -
        8 * X + 24 * X ^ 2 - 32 * X ^ 3 + 16 * X ^ 4 = 0 := by
    unfold euler
    linear_combination -(S * hdS - 2 * derivative ℚ S * hS - 2 * R * hdG + Rp * hG)
  have h1 : 1 ≤ n + 1 := by omega
  have h2 : 2 ≤ n + 1 := by omega
  have h3 : 3 ≤ n + 1 := by omega
  have h4 : 4 ≤ n + 1 := by omega
  have h5 : 5 ≤ n + 1 := by omega
  have h6 : 6 ≤ n + 1 := by omega
  have hc := congrArg (coeff (n + 1)) hEuler
  simp only [map_add, map_sub, map_zero, coeff_numeral_mul, coeff_shift_one _ _ h1,
    coeff_X_pow_mul', if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_pos h6,
    coeff_X, coeff_X_pow, coeff_euler] at hc
  have hn1 : n + 1 ≠ 1 := by omega
  have hn2 : n + 1 ≠ 2 := by omega
  have hn3 : n + 1 ≠ 3 := by omega
  have hn4 : n + 1 ≠ 4 := by omega
  simp only [hn1, hn2, hn3, hn4, ↓reduceIte, mul_zero, add_zero, sub_zero] at hc
  have hs1 : n + 1 - 1 = n := by omega
  have hs2 : n + 1 - 2 = n - 1 := by omega
  have hs3 : n + 1 - 3 = n - 2 := by omega
  have hs4 : n + 1 - 4 = n - 3 := by omega
  have hs5 : n + 1 - 5 = n - 4 := by omega
  have hs6 : n + 1 - 6 = n - 5 := by omega
  rw [hs1, hs2, hs3, hs4, hs5, hs6] at hc
  have hm1 : 1 ≤ n := by omega
  have hm2 : 2 ≤ n := by omega
  have hm3 : 3 ≤ n := by omega
  have hm4 : 4 ≤ n := by omega
  rw [Nat.cast_sub hm1, Nat.cast_sub hm2, Nat.cast_sub hm3, Nat.cast_sub hm4, Nat.cast_sub hn] at hc
  linear_combination hc / 4
