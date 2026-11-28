import OMAStatements.S_oeis_a239201

namespace OMA.A239201Proof

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

private lemma radical_ode (S : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2) :
    (1 - 6 * X + 5 * X ^ 2) * derivative ℚ S = (-3 + 5 * X) * S := by
  have hd := congrArg (derivative ℚ) hS
  simp [map_add, map_sub, Derivation.leibniz, smul_eq_mul, derivative_numeral] at hd
  apply mul_left_cancel₀ (numeral_ne_zero 2 (by norm_num))
  linear_combination S * hd - 2 * derivative ℚ S * hS

private lemma generating_ode (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2)
    (hS0 : coeff 0 S = 1)
    (hG : G * ((3 * X ^ 2 - 4 * X + 1) * S + 5 * X ^ 3 - 11 * X ^ 2 + 7 * X - 1) =
      -(X * S - 2 * X ^ 3 + 3 * X ^ 2 - X)) :
    (-1 + 7 * X - 11 * X ^ 2 + 5 * X ^ 3) * euler G +
      (1 - 4 * X + 3 * X ^ 2) * G = X ^ 2 := by
  have hRat : 4 * X ^ 2 * (1 - X) * S * G = 2 * X ^ 3 * (3 - 3 * X + S) := by
    linear_combination (1 - 3 * X + S) * hG - ((3 * X ^ 2 - 4 * X + 1) * G + X) * hS
  have hFactorX : (2 : ℚ⟦X⟧) * X ^ 2 ≠ 0 :=
    mul_ne_zero (numeral_ne_zero 2 (by norm_num)) (pow_ne_zero _ X_ne_zero)
  have hSimp : 2 * (1 - X) * S * G = X * (3 - 3 * X + S) := by
    apply mul_left_cancel₀ hFactorX
    linear_combination hRat
  let F : ℚ⟦X⟧ := 2 * (1 - X) * G - X
  have hFS : F * S = 3 * X * (1 - X) := by
    dsimp [F]
    linear_combination hSimp
  have hFSd := congrArg (derivative ℚ) hFS
  simp [Derivation.leibniz, smul_eq_mul, derivative_numeral] at hFSd
  have hS_ne : S ≠ 0 := by
    intro h
    rw [h, map_zero] at hS0
    norm_num at hS0
  have hOneSubX_ne : (1 - X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h0 := congrArg (coeff 0) h
    simp at h0
  have hFode_mul : S * (X * (1 - X) * (1 - 6 * X + 5 * X ^ 2) * derivative ℚ F -
      (1 - X) * (1 - 4 * X + 5 * X ^ 2) * F) = 0 := by
    linear_combination X * (1 - X) * (1 - 6 * X + 5 * X ^ 2) * hFSd -
      X * (1 - X) * F * radical_ode S hS - (1 - 6 * X + 5 * X ^ 2) * (1 - 2 * X) * hFS
  have hFode_oneSubX : (1 - X) * (X * (1 - 6 * X + 5 * X ^ 2) * derivative ℚ F -
      (1 - 4 * X + 5 * X ^ 2) * F) = 0 := by
    have h := mul_left_cancel₀ hS_ne (by linear_combination hFode_mul :
      S * ((1 - X) * (X * (1 - 6 * X + 5 * X ^ 2) * derivative ℚ F -
        (1 - 4 * X + 5 * X ^ 2) * F)) = S * 0)
    exact h
  have hFode : X * (1 - 6 * X + 5 * X ^ 2) * derivative ℚ F =
      (1 - 4 * X + 5 * X ^ 2) * F := by
    have h := mul_left_cancel₀ hOneSubX_ne (by linear_combination hFode_oneSubX :
      (1 - X) * (X * (1 - 6 * X + 5 * X ^ 2) * derivative ℚ F -
        (1 - 4 * X + 5 * X ^ 2) * F) = (1 - X) * 0)
    linear_combination h
  have hFd : derivative ℚ F = 2 * (1 - X) * derivative ℚ G - 2 * G - 1 := by
    dsimp [F]
    simp [Derivation.leibniz, smul_eq_mul, derivative_numeral]
    ring
  rw [hFd] at hFode
  have hEq : (2 : ℚ⟦X⟧) * ((-1 + 7 * X - 11 * X ^ 2 + 5 * X ^ 3) * euler G +
      (1 - 4 * X + 3 * X ^ 2) * G) = (2 : ℚ⟦X⟧) * X ^ 2 := by
    unfold euler
    dsimp only [F] at hFode
    linear_combination -hFode
  exact mul_left_cancel₀ (numeral_ne_zero 2 (by norm_num)) hEq

theorem recurrence (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2)
    (hS0 : coeff 0 S = 1)
    (hG : G * ((3 * X ^ 2 - 4 * X + 1) * S + 5 * X ^ 3 - 11 * X ^ 2 + 7 * X - 1) =
      -(X * S - 2 * X ^ 3 + 3 * X ^ 2 - X))
    (n : ℕ) (hn : 3 ≤ n) :
    (1 - (n : ℚ)) * coeff n G + (-11 + 7 * (n : ℚ)) * coeff (n - 1) G +
      (25 - 11 * (n : ℚ)) * coeff (n - 2) G + (-15 + 5 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  have hExpanded : -euler G + 7 * (X * euler G) - 11 * (X ^ 2 * euler G) + 5 * (X ^ 3 * euler G) +
      G - 4 * (X * G) + 3 * (X ^ 2 * G) = X ^ 2 := by
    linear_combination generating_ode S G hS hS0 hG
  have hc := congrArg (coeff n) hExpanded
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  simp only [map_add, map_sub, map_neg, coeff_numeral_mul, coeff_shift_one _ _ hn1,
    coeff_X_pow_mul', if_pos hn2, if_pos hn, coeff_euler, coeff_X_pow,
    if_neg (show n ≠ 2 by omega)] at hc
  rw [Nat.cast_sub hn1, Nat.cast_sub hn2, Nat.cast_sub hn] at hc
  push_cast at hc
  linear_combination hc

end OMA.A239201Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a239201.main := by
  intro S G hS hS0 hG n hn
  exact OMA.A239201Proof.recurrence S G hS hS0 hG n hn
