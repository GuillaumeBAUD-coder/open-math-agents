import OMAStatements.S_oeis_a085387

open PowerSeries

private theorem derivative_u :
    derivative ℚ OMA.S_oeis_a085387.u = 1 + X := by
  unfold OMA.S_oeis_a085387.u
  simp only [map_add, pow_two, Derivation.leibniz, derivative_C, derivative_X,
    smul_eq_mul, mul_zero, add_zero, mul_one]
  have hhalf : C (1 / 2 : ℚ) * (X + X) = X := by
    rw [← two_mul, ← mul_assoc, ← map_ofNat C 2, ← map_mul]
    norm_num
  rw [hhalf]

private theorem egf_ode :
    let F := OMA.S_oeis_a085387.egf
    derivative ℚ (derivative ℚ (derivative ℚ F)) - C 3 * derivative ℚ (derivative ℚ F) +
      (C 2 - C 2 * X - X ^ 2) * derivative ℚ F +
      (-C 3 - X + X ^ 2) * F = 0 := by
  intro F
  set u := OMA.S_oeis_a085387.u
  have hdu : derivative ℚ u = 1 + X := derivative_u
  set P : ℚ⟦X⟧ := exp ℚ * (exp ℚ).subst u
  set Q : ℚ⟦X⟧ := exp ℚ * (exp ℚ).subst (-u)
  have hu : HasSubst u := HasSubst.of_constantCoeff_zero' (by simp [u, OMA.S_oeis_a085387.u])
  have hnu : HasSubst (-u) := HasSubst.of_constantCoeff_zero' (by simp [u, OMA.S_oeis_a085387.u])
  have hdP : derivative ℚ P = (C 2 + X) * P := by
    dsimp only [P]
    simp only [Derivation.leibniz, derivative_exp, derivative_subst hu, hdu, smul_eq_mul]
    simp only [map_ofNat]
    ring
  have hdQ : derivative ℚ Q = (-X) * Q := by
    dsimp only [Q]
    simp only [Derivation.leibniz, derivative_exp, derivative_subst hnu, map_neg, hdu,
      smul_eq_mul]
    ring
  have hdP2 : derivative ℚ (derivative ℚ P) = (C 5 + C 4 * X + X ^ 2) * P := by
    rw [hdP]
    simp only [Derivation.leibniz, map_add, derivative_C, derivative_X, hdP, smul_eq_mul, zero_add]
    simp only [map_ofNat]
    ring
  have hdP3 :
      derivative ℚ (derivative ℚ (derivative ℚ P)) =
        (C 14 + C 15 * X + C 6 * X ^ 2 + X ^ 3) * P := by
    rw [hdP2]
    simp only [Derivation.leibniz, map_add, derivative_C, derivative_X, pow_two, hdP, smul_eq_mul,
      zero_mul, add_zero, zero_add, mul_one]
    simp only [map_ofNat]
    ring
  have hdQ2 : derivative ℚ (derivative ℚ Q) = (-1 + X ^ 2) * Q := by
    rw [hdQ]
    simp only [Derivation.leibniz, map_neg, derivative_X, hdQ, smul_eq_mul]
    ring
  have hdQ3 : derivative ℚ (derivative ℚ (derivative ℚ Q)) = (C 3 * X - X ^ 3) * Q := by
    rw [hdQ2]
    simp only [Derivation.leibniz, map_add, map_neg, derivative_one, pow_two, derivative_X, hdQ,
      smul_eq_mul, neg_zero, zero_add, mul_one, one_mul]
    simp only [map_ofNat]
    ring
  have hP_ode :
      derivative ℚ (derivative ℚ (derivative ℚ P)) - C 3 * derivative ℚ (derivative ℚ P) +
        (C 2 - C 2 * X - X ^ 2) * derivative ℚ P + (-C 3 - X + X ^ 2) * P = 0 := by
    rw [hdP3, hdP2, hdP]
    simp only [map_ofNat]
    ring
  have hQ_ode :
      derivative ℚ (derivative ℚ (derivative ℚ Q)) - C 3 * derivative ℚ (derivative ℚ Q) +
        (C 2 - C 2 * X - X ^ 2) * derivative ℚ Q + (-C 3 - X + X ^ 2) * Q = 0 := by
    rw [hdQ3, hdQ2, hdQ]
    simp only [map_ofNat]
    ring
  have hF : F = C (1 / 2 : ℚ) * (P + Q) := by
    dsimp only [F, OMA.S_oeis_a085387.egf, P, Q, u]
    ring
  have hdF : derivative ℚ F = C (1 / 2 : ℚ) * (derivative ℚ P + derivative ℚ Q) := by
    rw [hF]
    simp only [Derivation.leibniz, derivative_C, map_add, smul_eq_mul, mul_zero, add_zero]
  have hdF2 :
      derivative ℚ (derivative ℚ F) =
        C (1 / 2 : ℚ) * (derivative ℚ (derivative ℚ P) + derivative ℚ (derivative ℚ Q)) := by
    rw [hdF]
    simp only [Derivation.leibniz, derivative_C, map_add, smul_eq_mul, mul_zero, add_zero]
  have hdF3 :
      derivative ℚ (derivative ℚ (derivative ℚ F)) =
        C (1 / 2 : ℚ) *
          (derivative ℚ (derivative ℚ (derivative ℚ P)) +
            derivative ℚ (derivative ℚ (derivative ℚ Q))) := by
    rw [hdF2]
    simp only [Derivation.leibniz, derivative_C, map_add, smul_eq_mul, mul_zero, add_zero]
  rw [hdF3, hdF2, hdF, hF]
  linear_combination C (1 / 2 : ℚ) * (hP_ode + hQ_ode)

theorem OMA.solution : type_of% @OMA.S_oeis_a085387.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have hode :
      derivative ℚ (derivative ℚ (derivative ℚ OMA.S_oeis_a085387.egf)) -
        C 3 * derivative ℚ (derivative ℚ OMA.S_oeis_a085387.egf) +
        C 2 * derivative ℚ OMA.S_oeis_a085387.egf -
        C 2 * (X * derivative ℚ OMA.S_oeis_a085387.egf) -
        X ^ 2 * derivative ℚ OMA.S_oeis_a085387.egf -
        C 3 * OMA.S_oeis_a085387.egf -
        X * OMA.S_oeis_a085387.egf +
        X ^ 2 * OMA.S_oeis_a085387.egf = 0 := by
    linear_combination egf_ode
  have hc := congrArg (fun f => ((m + 2).factorial : ℚ) * coeff (m + 2) f) hode
  simp only [map_add, map_sub, map_zero, mul_zero, coeff_C_mul, coeff_X_pow_mul,
    coeff_succ_X_mul, coeff_derivative] at hc
  simp only [show m + 2 + 1 + 1 + 1 = m + 5 by omega,
    show m + 2 + 1 + 1 = m + 4 by omega,
    show m + 2 + 1 = m + 3 by omega,
    show m + 1 + 1 = m + 2 by omega] at hc
  simp only [OMA.S_oeis_a085387.a,
    show m + 5 - 1 = m + 4 by omega,
    show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega,
    show m + 5 - 4 = m + 1 by omega,
    show m + 5 - 5 = m by omega]
  have hf5 : ((m + 5).factorial : ℚ) =
      ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) *
        (m.factorial : ℚ) := by
    simp only [Nat.factorial_succ]
    push_cast
    ring
  have hf4 : ((m + 4).factorial : ℚ) =
      ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    simp only [Nat.factorial_succ]
    push_cast
    ring
  have hf3 : ((m + 3).factorial : ℚ) =
      ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    simp only [Nat.factorial_succ]
    push_cast
    ring
  have hf2 : ((m + 2).factorial : ℚ) = ((m : ℚ) + 2) * ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    simp only [Nat.factorial_succ]
    push_cast
    ring
  have hf1 : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    simp only [Nat.factorial_succ]
    push_cast
    ring
  rw [hf2] at hc
  rw [hf5, hf4, hf3, hf2, hf1]
  push_cast at hc ⊢
  linear_combination hc
