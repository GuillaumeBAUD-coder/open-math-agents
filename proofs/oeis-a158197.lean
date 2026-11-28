import OMAStatements.S_oeis_a158197

open PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a158197.main := by
  intro S c G hSq _ hCatalan hInv n hn

  have nat_ne_zero (m : ℕ) (hm : m ≠ 0) : (m : ℚ⟦X⟧) ≠ 0 := by
    intro h
    apply hm
    exact Nat.cast_eq_zero.mp (by
      simpa only [map_natCast, map_zero] using congrArg (constantCoeff (R := ℚ)) h)
  have X_mul_cancel : ∀ F H : ℚ⟦X⟧, X * F = X * H → F = H := by
    intro F H h
    ext m
    have h' := congrArg (coeff (m + 1)) h
    simpa only [coeff_succ_X_mul] using h'

  have hU : 2 * X ^ 2 * c ^ 2 = 1 - 2 * X - S := by
    apply mul_left_cancel₀ (nat_ne_zero 2 (by decide))
    linear_combination (2 * X * c + (1 - S)) * hCatalan + hSq
  have hFactor : 2 * X * G * (-2 + 5 * X + 2 * S) = -1 + 4 * X + (1 - 2 * X) * S := by
    apply mul_left_cancel₀ (nat_ne_zero 2 (by decide))
    linear_combination 4 * X ^ 2 * hInv + (8 * X * G - (2 * X ^ 2 * c ^ 2 + 1 - 2 * X - S)) * hU - hSq
  have hRationalized : 2 * X * (25 * X - 4) * G = -1 + 4 * X + (1 - 10 * X) * S := by
    apply X_mul_cancel
    linear_combination (-2 + 5 * X - 2 * S) * hFactor + (8 * X * G - 2 * (1 - 2 * X)) * hSq

  have derivative_nat (m : ℕ) : derivative ℚ (m : ℚ⟦X⟧) = 0 :=
    (derivative ℚ).map_natCast m
  have hSquareDerivative : (1 - 4 * X) * derivative ℚ S = -2 * S := by
    have h := congrArg (fun F : ℚ⟦X⟧ => derivative ℚ F) hSq
    change derivative ℚ (S ^ 2) = derivative ℚ (1 - 4 * X) at h
    simp only [derivative_pow, Nat.reduceSub, pow_one, Nat.cast_ofNat, map_sub,
      Derivation.leibniz, smul_eq_mul, derivative_one, derivative_X,
      show derivative ℚ (4 : ℚ⟦X⟧) = 0 from derivative_nat 4,
      mul_zero, add_zero] at h
    apply mul_left_cancel₀ (nat_ne_zero 2 (by decide))
    linear_combination S * h - 2 * derivative ℚ S * hSq
  have hProductDerivative :
      (100 * X - 8) * G + (50 * X ^ 2 - 8 * X) * derivative ℚ G =
        4 - 10 * S + (1 - 10 * X) * derivative ℚ S := by
    have h := congrArg (fun F : ℚ⟦X⟧ => derivative ℚ F) hRationalized
    change derivative ℚ (2 * X * (25 * X - 4) * G) =
      derivative ℚ (-1 + 4 * X + (1 - 10 * X) * S) at h
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_sub, map_neg,
      derivative_one, derivative_X,
      show derivative ℚ (2 : ℚ⟦X⟧) = 0 from derivative_nat 2,
      show derivative ℚ (25 : ℚ⟦X⟧) = 0 from derivative_nat 25,
      show derivative ℚ (4 : ℚ⟦X⟧) = 0 from derivative_nat 4,
      show derivative ℚ (10 : ℚ⟦X⟧) = 0 from derivative_nat 10,
      mul_zero, add_zero, zero_add, neg_zero, mul_one] at h
    linear_combination h
  have hDifferential :
      (4 - 81 * X + 510 * X ^ 2 - 1000 * X ^ 3) * (X * derivative ℚ G) +
        (4 - 58 * X + 320 * X ^ 2 - 500 * X ^ 3) * G = 4 - 26 * X + 40 * X ^ 2 := by
    apply mul_left_cancel₀ (nat_ne_zero 2 (by decide))
    linear_combination -((1 - 10 * X) * (1 - 4 * X) * hProductDerivative +
      (1 - 10 * X) ^ 2 * hSquareDerivative + (12 - 60 * X) * hRationalized)

  let E := X * derivative ℚ G
  have hEuler : C 4 * E - C 81 * (X * E) + C 510 * (X ^ 2 * E) - C 1000 * (X ^ 3 * E) +
      C 4 * G - C 58 * (X * G) + C 320 * (X ^ 2 * G) - C 500 * (X ^ 3 * G) =
      C 4 - C 26 * X + C 40 * X ^ 2 := by
    dsimp [E]
    simp only [map_ofNat]
    linear_combination hDifferential
  have coeff_E (k : ℕ) : coeff k E = (k : ℚ) * coeff k G := by
    cases k with
    | zero => simp [E, coeff_zero_eq_constantCoeff]
    | succ k =>
      dsimp [E]
      rw [coeff_succ_X_mul, coeff_derivative, Nat.cast_add, Nat.cast_one, mul_comm]

  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 3 := ⟨n - 3, by omega⟩
  have coeff_X2 (F : ℚ⟦X⟧) : coeff (k + 3) (X ^ 2 * F) = coeff (k + 1) F := by
    rw [show k + 3 = k + 1 + 2 from rfl, coeff_X_pow_mul]
  have h := congrArg (fun F : ℚ⟦X⟧ => coeff (k + 3) F) hEuler
  change coeff (k + 3) _ = coeff (k + 3) _ at h
  simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_X_pow_mul,
    coeff_X2, coeff_E, coeff_C, coeff_X, coeff_X_pow,
    if_neg (show k + 3 ≠ 0 by omega),
    if_neg (show k + 3 ≠ 1 by omega),
    if_neg (show k + 3 ≠ 2 by omega),
    mul_zero, sub_zero, add_zero] at h
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  simp only [Nat.cast_add, Nat.cast_ofNat] at h ⊢
  linear_combination h
