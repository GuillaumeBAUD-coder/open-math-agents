import OMAStatements.S_oeis_a132864

open PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a132864.main := by
  intro S c G hSq _ hCatalan hInv n hn

  have nat_ne_zero (m : ℕ) (hm : m ≠ 0) : (m : ℚ⟦X⟧) ≠ 0 := by
    intro h
    apply hm
    exact Nat.cast_eq_zero.mp (by
      simpa only [map_natCast, map_zero] using congrArg (constantCoeff (R := ℚ)) h)
  have hFactor : (3 + 2 * S) * G = 5 := by
    linear_combination 5 * hInv + 2 * G * hCatalan
  have hRationalized : (1 + 16 * X) * G = 3 - 2 * S := by
    apply mul_left_cancel₀ (nat_ne_zero 5 (by decide))
    linear_combination (3 - 2 * S) * hFactor + 4 * G * hSq

  have derivative_nat (m : ℕ) : derivative ℚ (m : ℚ⟦X⟧) = 0 :=
    (derivative ℚ).map_natCast m
  have hSquareDerivative : (1 - 20 * X) * derivative ℚ S = -10 * S := by
    have h := congrArg (fun F : ℚ⟦X⟧ => derivative ℚ F) hSq
    change derivative ℚ (S ^ 2) = derivative ℚ (1 - 20 * X) at h
    simp only [derivative_pow, Nat.reduceSub, pow_one, Nat.cast_ofNat, map_sub,
      Derivation.leibniz, smul_eq_mul, derivative_one, derivative_X,
      show derivative ℚ (20 : ℚ⟦X⟧) = 0 from derivative_nat 20,
      mul_zero, add_zero] at h
    apply mul_left_cancel₀ (nat_ne_zero 2 (by decide))
    linear_combination S * h - 2 * derivative ℚ S * hSq
  have hProductDerivative :
      16 * G + (1 + 16 * X) * derivative ℚ G = -2 * derivative ℚ S := by
    have h := congrArg (fun F : ℚ⟦X⟧ => derivative ℚ F) hRationalized
    change derivative ℚ ((1 + 16 * X) * G) = derivative ℚ (3 - 2 * S) at h
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_sub, derivative_one,
      derivative_X, show derivative ℚ (16 : ℚ⟦X⟧) = 0 from derivative_nat 16,
      show derivative ℚ (3 : ℚ⟦X⟧) = 0 from derivative_nat 3,
      show derivative ℚ (2 : ℚ⟦X⟧) = 0 from derivative_nat 2,
      mul_zero, add_zero, zero_add, zero_sub] at h
    linear_combination h
  have hDifferential :
      (1 - 4 * X - 320 * X ^ 2) * derivative ℚ G + (26 - 160 * X) * G = 30 := by
    linear_combination (1 - 20 * X) * hProductDerivative - 2 * hSquareDerivative +
      10 * hRationalized

  -- Multiplying by X makes the coefficient identity valid at n = 2 as well.
  let E := X * derivative ℚ G
  have hEuler : E - C 4 * (X * E) - C 320 * (X ^ 2 * E) +
      C 26 * (X * G) - C 160 * (X ^ 2 * G) = C 30 * X := by
    dsimp [E]
    simp only [map_ofNat]
    linear_combination X * hDifferential
  have coeff_E (k : ℕ) : coeff k E = (k : ℚ) * coeff k G := by
    cases k with
    | zero => simp [E, coeff_zero_eq_constantCoeff]
    | succ k =>
      dsimp [E]
      rw [coeff_succ_X_mul, coeff_derivative, Nat.cast_add, Nat.cast_one, mul_comm]

  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  have h := congrArg (fun F : ℚ⟦X⟧ => coeff (k + 2) F) hEuler
  change coeff (k + 2) _ = coeff (k + 2) _ at h
  simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_X_pow_mul, coeff_E,
    coeff_X, if_neg (show k + 2 ≠ 1 by omega), mul_zero] at h
  rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h ⊢
  linear_combination h
