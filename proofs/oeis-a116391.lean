import OMAStatements.S_oeis_a116391

open PowerSeries

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private noncomputable def euler (G : ℚ⟦X⟧) := X * derivative ℚ G

private theorem coeff_euler (n : ℕ) (G : ℚ⟦X⟧) :
    coeff n (euler G) = (n : ℚ) * coeff n G := by
  cases n with
  | zero => simp [euler]
  | succ n => rw [euler, coeff_succ_X_mul, coeff_derivative, mul_comm, Nat.cast_succ]

private theorem coeff_shift (n k : ℕ) (h : k ≤ n) (G : ℚ⟦X⟧) :
    coeff n (X ^ k * G) = coeff (n - k) G := by
  conv_lhs => rw [← Nat.sub_add_cancel h]
  exact coeff_X_pow_mul G k (n - k)

theorem OMA.solution : type_of% @OMA.S_oeis_a116391.main := by
  intro S G hSq _ hG n hn
  let H := (1 + X) * G
  have hH : H * (S - X) = 1 := by
    dsimp [H]
    linear_combination hG
  have hS : (1 - 4 * X ^ 2) * derivative ℚ S = -4 * X * S := by
    have hd := congrArg (fun f => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    have ht : (2 : ℚ⟦X⟧) ≠ 0 := by
      intro h
      have hc := congrArg (constantCoeff (R := ℚ)) h
      rw [← map_ofNat C 2, constantCoeff_C, map_zero] at hc
      norm_num at hc
    apply mul_left_cancel₀ ht
    linear_combination S * hd - 2 * derivative ℚ S * hSq
  have hHd := congrArg (fun f => derivative ℚ f) hH
  simp only [Derivation.leibniz, smul_eq_mul, map_sub, derivative_X,
    Derivation.map_one_eq_zero] at hHd
  have hODE : (1 - 9 * X ^ 2 + 20 * X ^ 4) * derivative ℚ H -
      (6 * X - 20 * X ^ 3) * H = 1 := by
    linear_combination (1 - 4 * X ^ 2) * (S + X) * hHd - H * (S + X) * hS -
      ((1 - 4 * X ^ 2) * derivative ℚ H - 4 * X * H) * hSq + hH
  have hEuler : euler G + X ^ 1 * (euler G + G) -
      X ^ 2 * (9 * euler G + 6 * G) - X ^ 3 * (9 * euler G + 15 * G) +
      X ^ 4 * (20 * euler G + 20 * G) + X ^ 5 * (20 * euler G + 40 * G) = X := by
    dsimp only [H] at hODE
    simp only [Derivation.leibniz, smul_eq_mul, map_add, Derivation.map_one_eq_zero,
      derivative_X, zero_add, mul_one] at hODE
    dsimp only [euler]
    linear_combination X * hODE
  have hc := congrArg (coeff n) hEuler
  have h1 : n ≠ 1 := by omega
  simp only [map_add, map_sub, coeff_shift n 1 (by omega), coeff_shift n 2 (by omega),
    coeff_shift n 3 (by omega), coeff_shift n 4 (by omega), coeff_shift n 5 hn,
    ← map_ofNat C, coeff_C_mul, coeff_euler, coeff_X, if_neg h1] at hc
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_sub hn] at hc
  push_cast at hc
  linear_combination hc
