import OMAStatements.S_oeis_a306948

section Proof

open PowerSeries

private lemma coeff_mul_X_succ (f : PowerSeries ℚ) (m : ℕ) :
    coeff (m + 1) (f * X) = coeff m f := by
  simp

private lemma egf_ode :
    d⁄dX OMA.S_oeis_a306948.egf + d⁄dX OMA.S_oeis_a306948.egf * X -
      PowerSeries.C (2 : ℚ) * OMA.S_oeis_a306948.egf - OMA.S_oeis_a306948.egf * X =
      exp ℚ + exp ℚ * X := by
  have hlog : d⁄dX ((1 + (X : PowerSeries ℚ)) * log ℚ) = 1 + log ℚ := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, derivative_one, derivative_X,
      zero_add, mul_one, mul_comm (1 + X), derivative_log_mul_one_add_X, add_comm]
  have hegf :
      d⁄dX OMA.S_oeis_a306948.egf =
        OMA.S_oeis_a306948.egf + (1 + log ℚ) * exp ℚ := by
    unfold OMA.S_oeis_a306948.egf
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_exp, hlog, mul_comm (exp ℚ)]
  have hmul :
      (1 + (X : PowerSeries ℚ)) * ((1 + log ℚ) * exp ℚ) =
        OMA.S_oeis_a306948.egf + exp ℚ + exp ℚ * X := by
    unfold OMA.S_oeis_a306948.egf
    ring
  have hC2 : PowerSeries.C (2 : ℚ) = 2 :=
    map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
  rw [hC2]
  linear_combination (1 + (X : PowerSeries ℚ)) * hegf + hmul

private lemma rec1 (m : ℕ) :
    OMA.S_oeis_a306948.a (m + 2) + ((m : ℚ) - 1) * OMA.S_oeis_a306948.a (m + 1) -
      ((m : ℚ) + 1) * OMA.S_oeis_a306948.a m = (m : ℚ) + 2 := by
  have hcoeff := congrArg (PowerSeries.coeff (m + 1)) egf_ode
  simp only [map_add, map_sub, coeff_derivative, coeff_mul_X_succ, coeff_C_mul, coeff_exp] at hcoeff
  have hfac1 : ((m + 1).factorial : ℚ) ≠ 0 := by positivity
  have hfac0 : (m.factorial : ℚ) ≠ 0 := by positivity
  have hmul := congrArg (fun t : ℚ => ((m + 1).factorial : ℚ) * t) hcoeff
  dsimp at hmul
  have hf1 : ((m + 2).factorial : ℚ) = ((m + 1).factorial : ℚ) * ((m : ℚ) + 2) := by
    rw [Nat.factorial_succ (m + 1)]
    push_cast
    ring
  have hf0 : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    rw [Nat.factorial_succ m]
    push_cast
    ring
  have hrhs :
      ((m + 1).factorial : ℚ) * (1 / ((m + 1).factorial : ℚ) + 1 / (m.factorial : ℚ)) =
        (m : ℚ) + 2 := by
    rw [mul_add, mul_one_div_cancel hfac1, hf0, mul_assoc, mul_one_div_cancel hfac0]
    ring
  rw [hrhs] at hmul
  unfold OMA.S_oeis_a306948.a
  rw [hf1, show ((m : ℚ) + 1) * ((m.factorial : ℚ) * coeff m OMA.S_oeis_a306948.egf) =
      ((m + 1).factorial : ℚ) * coeff m OMA.S_oeis_a306948.egf by rw [hf0]; ring]
  push_cast at hmul
  rw [show m + 1 + 1 = m + 2 by rfl] at hmul
  linear_combination hmul

end Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a306948.main := by
  intro n hn
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hr0 := rec1 r
  have hr1 := rec1 (r + 1)
  have hr2 := rec1 (r + 2)
  push_cast at hr0 hr1 hr2 ⊢
  linear_combination hr2 - 2 * hr1 + hr0
