import OMAStatements.S_oeis_a097189

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

private theorem generating_function_ode (T G : ℚ⟦X⟧)
    (hT : T ^ 3 = 1 - 9 * X) (hT0 : coeff 0 T = 1)
    (hG : G * ((1 - 9 * X) + 2 * T ^ 2) = 3) :
    (1 - X) * (1 - 9 * X) ^ 2 * derivative ℚ (derivative ℚ G)
      + (1 - 9 * X) * (-4 * ((1 - 9 * X) + 4)) * derivative ℚ G
      + (36 - 180 * X) * G - 6 = 0 := by
  have h3 : (3 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    simp [map_ofNat] at hc
  have h9 : (9 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    simp [map_ofNat] at hc
  have hd1 : 3 * T ^ 2 * derivative ℚ T = -9 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hT
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hd
    linear_combination hd
  have hT1 : (1 - 9 * X) * derivative ℚ T = -3 * T := by
    apply mul_left_cancel₀ h3
    linear_combination T * hd1 - 3 * derivative ℚ T * hT
  have hT2 : (1 - 9 * X) * derivative ℚ (derivative ℚ T) = 6 * derivative ℚ T := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hT1
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hG1 : derivative ℚ G * ((1 - 9 * X) + 2 * T ^ 2)
      + G * (-9 + 4 * T * derivative ℚ T) = 0 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hG
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hd
    linear_combination hd
  have hG2 : derivative ℚ (derivative ℚ G) * ((1 - 9 * X) + 2 * T ^ 2)
      + 2 * derivative ℚ G * (-9 + 4 * T * derivative ℚ T)
      + G * (4 * (derivative ℚ T) ^ 2 + 4 * T * derivative ℚ (derivative ℚ T)) = 0 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hG1
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hd
    linear_combination hd
  have hP : ((1 - 9 * X) * derivative ℚ G) * ((1 - 9 * X) + 2 * T ^ 2) ^ 2
      = 3 * (9 * (1 - 9 * X) + 12 * T ^ 2) := by
    linear_combination ((1 - 9 * X) * ((1 - 9 * X) + 2 * T ^ 2)) * hG1
      + (9 * (1 - 9 * X) + 12 * T ^ 2) * hG
      - (4 * T * G * ((1 - 9 * X) + 2 * T ^ 2)) * hT1
  have hQ : ((1 - 9 * X) ^ 2 * derivative ℚ (derivative ℚ G)) * ((1 - 9 * X) + 2 * T ^ 2) ^ 3
      = 6 * (9 * (1 - 9 * X) + 12 * T ^ 2) ^ 2
        + 108 * T ^ 2 * ((1 - 9 * X) + 2 * T ^ 2) := by
    have hQ0 : ((1 - 9 * X) ^ 2 * derivative ℚ (derivative ℚ G)) * ((1 - 9 * X) + 2 * T ^ 2)
        = 2 * ((1 - 9 * X) * derivative ℚ G) * (9 * (1 - 9 * X) + 12 * T ^ 2)
          + 36 * G * T ^ 2 := by
      linear_combination (1 - 9 * X) ^ 2 * hG2
        - (8 * T * (1 - 9 * X) * derivative ℚ G
            + 4 * G * ((1 - 9 * X) * derivative ℚ T - 3 * T)
            + 24 * G * T) * hT1
        - (4 * G * T * (1 - 9 * X)) * hT2
    linear_combination ((1 - 9 * X) + 2 * T ^ 2) ^ 2 * hQ0
      + (2 * (9 * (1 - 9 * X) + 12 * T ^ 2)) * hP
      + (36 * T ^ 2 * ((1 - 9 * X) + 2 * T ^ 2)) * hG
  have hD : ((1 - 9 * X) + 2 * T ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    rw [coeff_zero_eq_constantCoeff_apply] at hT0
    simp [hT0, map_ofNat] at hc
    norm_num at hc
  apply mul_left_cancel₀ (mul_ne_zero h9 (pow_ne_zero 3 hD))
  linear_combination (8 + (1 - 9 * X)) * hQ
    - (36 * ((1 - 9 * X) + 4) * ((1 - 9 * X) + 2 * T ^ 2)) * hP
    + (9 * (16 + 20 * (1 - 9 * X)) * ((1 - 9 * X) + 2 * T ^ 2) ^ 2) * hG
    - (432 * (T ^ 3 + (1 - 9 * X))) * hT

theorem OMA.solution : type_of% @OMA.S_oeis_a097189.main := by
  intro T G hT hT0 hG _ n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hode := generating_function_ode T G hT hT0 hG
  have htheta : X * derivative ℚ (X * derivative ℚ G)
      = X * derivative ℚ G + X ^ 2 * derivative ℚ (derivative ℚ G) := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hop : X * derivative ℚ (X * derivative ℚ G) - X * derivative ℚ G
      + X ^ 1 * (-(C 19 * (X * derivative ℚ (X * derivative ℚ G))) - X * derivative ℚ G)
      + X ^ 2 * (C 99 * (X * derivative ℚ (X * derivative ℚ G))
          + C 117 * (X * derivative ℚ G) + C 36 * G)
      + X ^ 3 * (-(C 81 * (X * derivative ℚ (X * derivative ℚ G)))
          - C 243 * (X * derivative ℚ G) - C 180 * G)
      = C 6 * X ^ 2 := by
    rw [htheta]
    simp only [map_ofNat]
    linear_combination X ^ 2 * hode
  have hc := congrArg (coeff (k + 3)) hop
  have e1 : ∀ f : ℚ⟦X⟧, coeff (k + 3) (X ^ 1 * f) = coeff (k + 2) f :=
    fun f => coeff_X_pow_mul f 1 (k + 2)
  have e2 : ∀ f : ℚ⟦X⟧, coeff (k + 3) (X ^ 2 * f) = coeff (k + 1) f :=
    fun f => coeff_X_pow_mul f 2 (k + 1)
  have e3 : ∀ f : ℚ⟦X⟧, coeff (k + 3) (X ^ 3 * f) = coeff k f :=
    fun f => coeff_X_pow_mul f 3 k
  have e0 : coeff (k + 3) (C (6 : ℚ) * X ^ 2) = 0 := by
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  rw [e0] at hc
  simp only [map_add, map_sub, map_neg, e1, e2, e3, coeff_C_mul, coeff_X_derivative] at hc
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  push_cast at hc ⊢
  linear_combination hc
