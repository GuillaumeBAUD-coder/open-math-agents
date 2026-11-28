import OMAStatements.S_oeis_a192989

open PowerSeries OMA.S_oeis_a192989

private theorem derivative_egf :
    derivative ℚ egf = C 3 * egf + C 6 * (X * egf) + C 3 * (X ^ 2 * egf) := by
  have hSubst : HasSubst ((1 + X : ℚ⟦X⟧) ^ 3 - 1) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  have hInner : derivative ℚ ((1 + X) ^ 3 - 1) = C 3 + C 6 * X + C 3 * X ^ 2 := by
    rw [map_ofNat C 3, map_ofNat C 6]
    simp [derivative_pow] <;> ring
  unfold egf
  rw [derivative_subst hSubst, derivative_exp, hInner]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a192989.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hc := congrArg (coeff (k + 2)) derivative_egf
  simp only [coeff_derivative, map_add, coeff_C_mul, coeff_succ_X_mul,
    coeff_X_pow_mul] at hc
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega, a]
  rw [Nat.factorial_succ (k + 2), Nat.factorial_succ (k + 1), Nat.factorial_succ k]
  push_cast at hc ⊢
  linear_combination (Nat.factorial k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) * hc
