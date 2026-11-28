import OMAStatements.S_oeis_a102880

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

private theorem ne_zero_of_const (f : ℚ⟦X⟧) (h : constantCoeff f ≠ 0) : f ≠ 0 := by
  intro hf
  apply h
  rw [hf, map_zero]

private theorem first_order :
    X * ((1 + X ^ 2) * (1 - 4 * X + X ^ 2)) * (1 - X ^ 2)
        * derivative ℚ OMA.S_oeis_a102880.A
      + (1 - 2 * X + 3 * X ^ 2 - 12 * X ^ 3 + 3 * X ^ 4 - 2 * X ^ 5 + X ^ 6)
        * OMA.S_oeis_a102880.A
      - (1 - X ^ 2) ^ 3 = 0 := by
  have hw0 : constantCoeff (1 + X ^ 2 : ℚ⟦X⟧) ≠ 0 := by simp
  have hwi : (1 + X ^ 2 : ℚ⟦X⟧) * (1 + X ^ 2)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hw0
  have hy : HasSubst (X * (1 + X ^ 2)⁻¹ : ℚ⟦X⟧) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  have hc : OMA.S_oeis_a102880.c ^ 2 * X + 1 = OMA.S_oeis_a102880.c := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
    simpa [OMA.S_oeis_a102880.c] using h
  set Cs : ℚ⟦X⟧ := OMA.S_oeis_a102880.c.subst (X * (1 + X ^ 2)⁻¹ : ℚ⟦X⟧) with hCs
  have hC : Cs ^ 2 * (X * (1 + X ^ 2)⁻¹) + 1 = Cs := by
    have h := congrArg (substAlgHom hy) hc
    simp only [map_add, map_mul, map_pow, map_one, substAlgHom_X] at h
    simpa only [coe_substAlgHom, ← hCs] using h
  have hquad : (1 + X ^ 2) * Cs = X * Cs ^ 2 + (1 + X ^ 2) := by
    linear_combination (-(1 + X ^ 2 : ℚ⟦X⟧)) * hC + (X * Cs ^ 2) * hwi
  have hA : OMA.S_oeis_a102880.A = (1 - X ^ 2) * (1 + X ^ 2)⁻¹ * Cs := rfl
  set A : ℚ⟦X⟧ := OMA.S_oeis_a102880.A
  set R : ℚ⟦X⟧ := 1 + X ^ 2 - 2 * X * Cs with hRdef
  have hR2 : R ^ 2 = (1 + X ^ 2) * (1 - 4 * X + X ^ 2) := by
    rw [hRdef]
    linear_combination (-4 * X : ℚ⟦X⟧) * hquad
  have hMA : 2 * X * (1 + X ^ 2) * A = (1 - X ^ 2) * (1 + X ^ 2) - (1 - X ^ 2) * R := by
    rw [hRdef, hA]
    linear_combination (2 * X * (1 - X ^ 2) * Cs) * hwi
  have h2 : (2 : ℚ⟦X⟧) ≠ 0 := ne_zero_of_const _ (by simp [map_ofNat])
  have hR0 : R ≠ 0 := ne_zero_of_const _ (by simp [hRdef])
  have hRd : (1 + X ^ 2) * (1 - 4 * X + X ^ 2) * derivative ℚ R
      = (-2 + 2 * X - 6 * X ^ 2 + 2 * X ^ 3) * R := by
    have hd : 2 * R * derivative ℚ R = -4 + 4 * X - 12 * X ^ 2 + 4 * X ^ 3 := by
      have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hR2
      simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hd
      linear_combination hd
    apply mul_left_cancel₀ (mul_ne_zero h2 hR0)
    linear_combination ((1 + X ^ 2) * (1 - 4 * X + X ^ 2) : ℚ⟦X⟧) * hd
      - (2 * (-2 + 2 * X - 6 * X ^ 2 + 2 * X ^ 3) : ℚ⟦X⟧) * hR2
  have hdMA : (2 + 6 * X ^ 2) * A + 2 * X * (1 + X ^ 2) * derivative ℚ A
      = -4 * X ^ 3 - (-2 * X) * R - (1 - X ^ 2) * derivative ℚ R := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hMA
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hd
    linear_combination hd
  have hw : (1 + X ^ 2 : ℚ⟦X⟧) ≠ 0 := ne_zero_of_const _ hw0
  apply mul_left_cancel₀ (mul_ne_zero h2 hw)
  linear_combination ((1 + X ^ 2) * (1 - 4 * X + X ^ 2) * (1 - X ^ 2) : ℚ⟦X⟧) * hdMA
    - ((1 + X ^ 2) * (1 - 4 * X + X ^ 2) * (-2 * X)
        + (1 - X ^ 2) * (-2 + 2 * X - 6 * X ^ 2 + 2 * X ^ 3) : ℚ⟦X⟧) * hMA
    - ((1 - X ^ 2) ^ 2 : ℚ⟦X⟧) * hRd

theorem OMA.solution : type_of% @OMA.S_oeis_a102880.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have hF := first_order
  set A : ℚ⟦X⟧ := OMA.S_oeis_a102880.A
  have hF' := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hF
  simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hF'
  have htheta : X * derivative ℚ (X * derivative ℚ A)
      = X * derivative ℚ A + X ^ 2 * derivative ℚ (derivative ℚ A) := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hK : (1 - X ^ 2 : ℚ⟦X⟧) ≠ 0 := ne_zero_of_const _ (by simp)
  have hop : X * derivative ℚ (X * derivative ℚ A) - C 2 * (X * derivative ℚ A) - C 3 * A
      + X ^ 1 * (-(C 4 * (X * derivative ℚ (X * derivative ℚ A)))
          + C 6 * (X * derivative ℚ A) + C 4 * A)
      + X ^ 2 * (C 2 * (X * derivative ℚ (X * derivative ℚ A)) - C 6 * A)
      + X ^ 3 * (-(C 4 * (X * derivative ℚ (X * derivative ℚ A)))
          - C 6 * (X * derivative ℚ A) + C 4 * A)
      + X ^ 4 * (X * derivative ℚ (X * derivative ℚ A)
          + C 2 * (X * derivative ℚ A) - C 3 * A)
      = C 3 * X ^ 4 - C 3 := by
    rw [htheta]
    simp only [map_ofNat]
    apply mul_left_cancel₀ hK
    linear_combination X * hF' - 3 * hF
  have hc := congrArg (coeff (k + 5)) hop
  have e1 : ∀ f : ℚ⟦X⟧, coeff (k + 5) (X ^ 1 * f) = coeff (k + 4) f :=
    fun f => coeff_X_pow_mul f 1 (k + 4)
  have e2 : ∀ f : ℚ⟦X⟧, coeff (k + 5) (X ^ 2 * f) = coeff (k + 3) f :=
    fun f => coeff_X_pow_mul f 2 (k + 3)
  have e3 : ∀ f : ℚ⟦X⟧, coeff (k + 5) (X ^ 3 * f) = coeff (k + 2) f :=
    fun f => coeff_X_pow_mul f 3 (k + 2)
  have e4 : ∀ f : ℚ⟦X⟧, coeff (k + 5) (X ^ 4 * f) = coeff (k + 1) f :=
    fun f => coeff_X_pow_mul f 4 (k + 1)
  have e0 : coeff (k + 5) (C (3 : ℚ) * X ^ 4 - C 3) = 0 := by
    rw [map_sub, coeff_C_mul, coeff_X_pow, if_neg (by omega), coeff_C, if_neg (by omega),
      mul_zero, sub_zero]
  rw [e0] at hc
  simp only [map_add, map_sub, map_neg, e1, e2, e3, e4, coeff_C_mul, coeff_X_derivative] at hc
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega]
  push_cast at hc ⊢
  linear_combination hc
