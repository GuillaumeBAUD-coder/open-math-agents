import OMAStatements.S_oeis_a087214

open PowerSeries OMA.S_oeis_a087214

private noncomputable def euler (G : ℚ⟦X⟧) := X * derivative ℚ G

private theorem coeff_euler (n : ℕ) (G : ℚ⟦X⟧) :
    coeff n (euler G) = (n : ℚ) * coeff n G := by
  cases n with
  | zero => simp [euler]
  | succ n => rw [euler, coeff_succ_X_mul, coeff_derivative, mul_comm, Nat.cast_succ]

theorem OMA.solution : type_of% @OMA.S_oeis_a087214.main := by
  intro n hn
  let P : ℚ⟦X⟧ := 1 - C (1 / 2) * X ^ 2
  have hP : constantCoeff P ≠ 0 := by simp [P]
  have hExp : P * E = PowerSeries.exp ℚ := by
    rw [E, smul_eq_C_mul]
    change P * (PowerSeries.exp ℚ * P⁻¹) = _
    rw [mul_left_comm, P.mul_inv_cancel hP, mul_one]
  have hHalf : C (1 / 2 : ℚ) * 2 = (1 : ℚ⟦X⟧) := by
    rw [← map_ofNat C 2, ← map_mul]
    norm_num
  have hD : derivative ℚ P = -X := by
    simp [P, Derivation.leibniz, smul_eq_mul]
    rw [one_div] at hHalf
    linear_combination X * hHalf
  have hd := congrArg (fun f => derivative ℚ f) hExp
  simp only [Derivation.leibniz, smul_eq_mul, hD, derivative_exp] at hd
  have hP2 : 2 * P = 2 - X ^ 2 := by
    dsimp [P]
    linear_combination -X ^ 2 * hHalf
  have hODE : 2 * euler E - 2 * (X * E) - X ^ 2 * euler E -
      2 * (X ^ 2 * E) + X ^ 3 * E = 0 := by
    dsimp only [euler]
    linear_combination 2 * X * hd - 2 * X * hExp -
      X * derivative ℚ E * hP2 + X * E * hP2
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hc := congrArg (coeff (k + 3)) hODE
  simp only [map_add, map_sub, ← map_ofNat C, coeff_C_mul, coeff_succ_X_mul,
    coeff_X_pow_mul (euler E) 2 (k + 1), coeff_X_pow_mul E 2 (k + 1),
    coeff_X_pow_mul E 3 k, coeff_euler, map_zero] at hc
  simp only [a, show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  rw [show (k + 3).factorial = (k + 3) * (k + 2).factorial from Nat.factorial_succ _,
      show (k + 2).factorial = (k + 2) * (k + 1).factorial from Nat.factorial_succ _,
      show (k + 1).factorial = (k + 1) * k.factorial from Nat.factorial_succ _]
  push_cast at hc ⊢
  linear_combination ((k : ℚ) + 2) * ((k : ℚ) + 1) * (k.factorial : ℚ) * hc
