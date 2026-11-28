import OMAStatements.S_oeis_a239204

namespace OMA.A239204Proof

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

private lemma radical_ode (S : ℚ⟦X⟧) (hS : S ^ 2 = X ^ 2 - 6 * X + 1) :
    (X ^ 2 - 6 * X + 1) * derivative ℚ S = (X - 3) * S := by
  have hd := congrArg (derivative ℚ) hS
  simp [map_add, map_sub, Derivation.leibniz, smul_eq_mul, derivative_numeral] at hd
  apply mul_left_cancel₀ (numeral_ne_zero 2 (by norm_num))
  linear_combination S * hd - 2 * derivative ℚ S * hS

private lemma generating_ode (S G : ℚ⟦X⟧) (hS : S ^ 2 = X ^ 2 - 6 * X + 1)
    (hG : 8 * X ^ 3 * G = (X - 1) * S - X ^ 2 - 4 * X + 1) :
    (1 - 7 * X + 7 * X ^ 2 - X ^ 3) * euler G +
      (3 - 17 * X + 11 * X ^ 2 - X ^ 3) * G = 3 - X := by
  let H : ℚ⟦X⟧ := (X - 1) * S
  have hH : 8 * X ^ 3 * G + X ^ 2 + 4 * X - 1 = H := by
    dsimp [H]
    linear_combination hG
  have hHd : derivative ℚ H = S + (X - 1) * derivative ℚ S := by
    simp [H, Derivation.leibniz, smul_eq_mul, add_comm]
  have hHode : ((X - 1) * (X ^ 2 - 6 * X + 1)) * derivative ℚ H =
      (2 * X ^ 2 - 10 * X + 4) * H := by
    rw [hHd]
    dsimp only [H]
    linear_combination (X - 1) ^ 2 * radical_ode S hS
  have hEulerH : euler H = 8 * X ^ 3 * (euler G + 3 * G) + 2 * X ^ 2 + 4 * X := by
    rw [← hH]
    simp [euler, Derivation.leibniz, smul_eq_mul, derivative_numeral]
    ring
  have hEulerODE : (1 - 7 * X + 7 * X ^ 2 - X ^ 3) * euler H +
      X * (2 * X ^ 2 - 10 * X + 4) * H = 0 := by
    unfold euler
    linear_combination -X * hHode
  rw [hEulerH, ← hH] at hEulerODE
  have hFactor : (8 : ℚ⟦X⟧) * X ^ 3 ≠ 0 :=
    mul_ne_zero (numeral_ne_zero 8 (by norm_num)) (pow_ne_zero _ X_ne_zero)
  apply mul_left_cancel₀ hFactor
  linear_combination hEulerODE

theorem recurrence (S G : ℚ⟦X⟧) (hS : S ^ 2 = X ^ 2 - 6 * X + 1)
    (hG : 8 * X ^ 3 * G = (X - 1) * S - X ^ 2 - 4 * X + 1) (n : ℕ) (hn : 3 ≤ n) :
    ((n : ℚ) + 3) * coeff n G + (-7 * (n : ℚ) - 10) * coeff (n - 1) G +
      (7 * (n : ℚ) - 3) * coeff (n - 2) G + (-(n : ℚ) + 2) * coeff (n - 3) G = 0 := by
  have hExpanded : euler G - 7 * (X * euler G) + 7 * (X ^ 2 * euler G) - X ^ 3 * euler G +
      3 * G - 17 * (X * G) + 11 * (X ^ 2 * G) - X ^ 3 * G = 3 * 1 - X := by
    linear_combination generating_ode S G hS hG
  have hc := congrArg (coeff n) hExpanded
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  simp only [map_add, map_sub, coeff_numeral_mul, coeff_shift_one _ _ hn1,
    coeff_X_pow_mul', if_pos hn2, if_pos hn, coeff_euler, coeff_one, coeff_X,
    if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega), mul_zero, sub_zero] at hc
  rw [Nat.cast_sub hn1, Nat.cast_sub hn2, Nat.cast_sub hn] at hc
  push_cast at hc
  linear_combination hc

end OMA.A239204Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a239204.main := by
  intro S G hS _ hG n hn
  exact OMA.A239204Proof.recurrence S G hS hG n hn
