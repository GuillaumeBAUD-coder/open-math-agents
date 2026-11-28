import OMAStatements.S_oeis_a212205

namespace OMA.A212205Proof

open PowerSeries

private lemma numeral_ne_zero (m : ℕ) [m.AtLeastTwo] (hm : (OfNat.ofNat m : ℚ) ≠ 0) :
    (OfNat.ofNat m : ℚ⟦X⟧) ≠ 0 := by
  rw [← map_ofNat C m, ← map_zero C]
  exact fun h => hm (C_injective h)

private lemma derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m, derivative_C]

private lemma coeff_numeral_mul (m n : ℕ) [m.AtLeastTwo] (F : ℚ⟦X⟧) :
    coeff n ((no_index (OfNat.ofNat m : ℚ⟦X⟧)) * F) = (OfNat.ofNat m : ℚ) * coeff n F := by
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

private lemma radical_ode (S : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X ^ 2 + X ^ 4) :
    (1 - 6 * X ^ 2 + X ^ 4) * derivative ℚ S = (-6 * X + 2 * X ^ 3) * S := by
  have hd := congrArg (derivative ℚ) hS
  simp [map_add, map_sub, Derivation.leibniz, smul_eq_mul, derivative_numeral] at hd
  apply mul_left_cancel₀ (numeral_ne_zero 2 (by norm_num))
  linear_combination S * hd - 2 * derivative ℚ S * hS

private lemma generating_ode (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X ^ 2 + X ^ 4)
    (hG : 2 * X * (1 - 6 * X ^ 2) * G = (1 + 2 * X) * S - 1 + 5 * X ^ 2 - 2 * X ^ 3) :
    (1 + 2 * X - 12 * X ^ 2 - 24 * X ^ 3 + 37 * X ^ 4 + 74 * X ^ 5 - 6 * X ^ 6 - 12 * X ^ 7) * euler G +
      (1 - 18 * X ^ 2 - 12 * X ^ 3 + 71 * X ^ 4 + 68 * X ^ 5 - 6 * X ^ 6) * G =
      1 + 2 * X - 10 * X ^ 2 - 18 * X ^ 3 + 15 * X ^ 4 + 12 * X ^ 5 - 6 * X ^ 6 := by
  let H : ℚ⟦X⟧ := (1 + 2 * X) * S
  have hH : 2 * X * (1 - 6 * X ^ 2) * G + 1 - 5 * X ^ 2 + 2 * X ^ 3 = H := by
    dsimp [H]
    linear_combination hG
  have hHd : derivative ℚ H = 2 * S + (1 + 2 * X) * derivative ℚ S := by
    simp [H, Derivation.leibniz, smul_eq_mul, derivative_numeral]
    ring
  have hHode : ((1 + 2 * X) * (1 - 6 * X ^ 2 + X ^ 4)) * derivative ℚ H =
      (2 * (1 - 6 * X ^ 2 + X ^ 4) + (1 + 2 * X) * (-6 * X + 2 * X ^ 3)) * H := by
    rw [hHd]
    dsimp only [H]
    linear_combination (1 + 2 * X) ^ 2 * radical_ode S hS
  have hEulerH : euler H =
      2 * X * (1 - 6 * X ^ 2) * euler G + (2 * X - 36 * X ^ 3) * G - 10 * X ^ 2 + 6 * X ^ 3 := by
    rw [← hH]
    simp [euler, Derivation.leibniz, smul_eq_mul, derivative_numeral]
    ring
  have hEulerODE : (1 + 2 * X) * (1 - 6 * X ^ 2 + X ^ 4) * euler H -
      X * (2 * (1 - 6 * X ^ 2 + X ^ 4) + (1 + 2 * X) * (-6 * X + 2 * X ^ 3)) * H = 0 := by
    unfold euler
    linear_combination X * hHode
  rw [hEulerH, ← hH] at hEulerODE
  have hFactor : (2 : ℚ⟦X⟧) * X ≠ 0 :=
    mul_ne_zero (numeral_ne_zero 2 (by norm_num)) X_ne_zero
  apply mul_left_cancel₀ hFactor
  linear_combination hEulerODE

theorem recurrence (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X ^ 2 + X ^ 4)
    (hG : 2 * X * (1 - 6 * X ^ 2) * G = (1 + 2 * X) * S - 1 + 5 * X ^ 2 - 2 * X ^ 3)
    (n : ℕ) (hn : 7 ≤ n) :
    (1 + (n : ℚ)) * coeff n G + (-2 + 2 * (n : ℚ)) * coeff (n - 1) G +
      (6 - 12 * (n : ℚ)) * coeff (n - 2) G + (60 - 24 * (n : ℚ)) * coeff (n - 3) G +
      (-77 + 37 * (n : ℚ)) * coeff (n - 4) G + (-302 + 74 * (n : ℚ)) * coeff (n - 5) G +
      (30 - 6 * (n : ℚ)) * coeff (n - 6) G + (84 - 12 * (n : ℚ)) * coeff (n - 7) G = 0 := by
  have hExpanded : euler G + 2 * (X * euler G) - 12 * (X ^ 2 * euler G) - 24 * (X ^ 3 * euler G) +
      37 * (X ^ 4 * euler G) + 74 * (X ^ 5 * euler G) - 6 * (X ^ 6 * euler G) - 12 * (X ^ 7 * euler G) +
      G - 18 * (X ^ 2 * G) - 12 * (X ^ 3 * G) + 71 * (X ^ 4 * G) + 68 * (X ^ 5 * G) - 6 * (X ^ 6 * G) =
      1 + 2 * X - 10 * X ^ 2 - 18 * X ^ 3 + 15 * X ^ 4 + 12 * X ^ 5 - 6 * X ^ 6 := by
    linear_combination generating_ode S G hS hG
  have hc := congrArg (coeff n) hExpanded
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hn4 : 4 ≤ n := by omega
  have hn5 : 5 ≤ n := by omega
  have hn6 : 6 ≤ n := by omega
  simp only [map_add, map_sub, coeff_numeral_mul, coeff_shift_one _ _ hn1,
    coeff_X_pow_mul', if_pos hn2, if_pos hn3, if_pos hn4, if_pos hn5, if_pos hn6, if_pos hn,
    coeff_euler, coeff_one, coeff_X, coeff_X_pow,
    if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega),
    if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega),
    if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega),
    if_neg (show n ≠ 6 by omega), mul_zero, add_zero, sub_zero] at hc
  rw [Nat.cast_sub hn1, Nat.cast_sub hn2, Nat.cast_sub hn3,
    Nat.cast_sub hn4, Nat.cast_sub hn5, Nat.cast_sub hn6, Nat.cast_sub hn] at hc
  push_cast at hc
  linear_combination hc

end OMA.A212205Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a212205.main := by
  intro S G hS _ hG n hn
  exact OMA.A212205Proof.recurrence S G hS hG n hn
