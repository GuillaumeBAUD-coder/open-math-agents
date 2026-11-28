import OMAStatements.S_oeis_a154623

namespace OMA.A154623Proof

open PowerSeries

private lemma series_two_ne_zero : (2 : ℚ⟦X⟧) ≠ 0 := by
  rw [← map_ofNat (C : ℚ →+* ℚ⟦X⟧) 2, ← map_zero (C : ℚ →+* ℚ⟦X⟧)]
  exact fun h => two_ne_zero (C_injective h)

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

private lemma radical_ode (T : ℚ⟦X⟧) (hT : T ^ 2 * (1 - 5 * X) = 1 - 9 * X) :
    (1 - 5 * X) * (1 - 9 * X) * derivative ℚ T = -2 * T := by
  have hd := congrArg (derivative ℚ) hT
  simp [map_sub, Derivation.leibniz, smul_eq_mul, derivative_pow,
    derivative_numeral, derivative_one] at hd
  have hCleared : 2 * T * (1 - 5 * X) ^ 2 * derivative ℚ T = -4 := by
    linear_combination (1 - 5 * X) * hd + 5 * hT
  apply mul_left_cancel₀ series_two_ne_zero
  linear_combination T * hCleared - (2 * (1 - 5 * X) * derivative ℚ T) * hT

private lemma generating_ode (T G : ℚ⟦X⟧)
    (hT : T ^ 2 * (1 - 5 * X) = 1 - 9 * X) (hG : 2 * G = 3 - T) :
    (1 - 14 * X + 45 * X ^ 2) * derivative ℚ G + 2 * G = 3 := by
  have hdG := congrArg (derivative ℚ) hG
  simp [map_sub, Derivation.leibniz, smul_eq_mul, derivative_numeral] at hdG
  apply mul_left_cancel₀ series_two_ne_zero
  linear_combination (1 - 5 * X) * (1 - 9 * X) * hdG - radical_ode T hT + 2 * hG

end OMA.A154623Proof

open PowerSeries OMA.A154623Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a154623.main := by
  intro T G hT _ hG n hn
  have hEuler : euler G - 14 * (X * euler G) + 45 * (X ^ 2 * euler G) +
      2 * (X * G) = 3 * X := by
    unfold euler
    linear_combination X * generating_ode T G hT hG
  have hc := congrArg (coeff n) hEuler
  have hn1 : 1 ≤ n := by omega
  simp only [map_add, map_sub, coeff_numeral_mul, coeff_shift_one _ _ hn1,
    coeff_X_pow_mul', if_pos hn, coeff_euler, coeff_X,
    if_neg (show n ≠ 1 by omega), mul_zero] at hc
  rw [Nat.cast_sub hn1, Nat.cast_sub hn] at hc
  push_cast at hc
  linear_combination hc
