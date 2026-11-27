import OMAStatements.S_oeis_a049425

/-!
Proof of OEIS A049425: differentiating the exponential generating function
series = exp.subst (X + X^2 + (1/3)*X^3) yields
derivative series = (1 + 2*X + X^2) * series.
Extracting the coefficient of X^(n+2) and multiplying by (n+2)! gives Mathar's recurrence.
-/

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a049425.main := by
  have hsub : HasSubst OMA.S_oeis_a049425.parameter :=
    HasSubst.of_constantCoeff_zero' (by simp [OMA.S_oeis_a049425.parameter])
  have hdparam : d⁄dX OMA.S_oeis_a049425.parameter = 1 + 2 * X + X ^ 2 := by
    unfold OMA.S_oeis_a049425.parameter
    rw [map_add, map_add, Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul,
      derivative_pow, derivative_pow, derivative_X]
    have hC : C (1 / 3 : ℚ) * ((3 : ℕ) : PowerSeries ℚ) = 1 := by
      rw [← map_natCast C 3, ← map_mul]
      norm_num
    simp only [Nat.add_one_sub_one, show 3 - 1 = 2 by decide, pow_one, mul_one]
    linear_combination X ^ 2 * hC
  have hderiv : d⁄dX OMA.S_oeis_a049425.series =
      (1 + 2 * X + X ^ 2) * OMA.S_oeis_a049425.series := by
    rw [OMA.S_oeis_a049425.series, derivative_subst hsub, derivative_exp, hdparam, mul_comm]
  intro n
  have hcoeff := congrArg (coeff (n + 2)) hderiv
  rw [coeff_derivative] at hcoeff
  have hrhs : (1 + 2 * (X : PowerSeries ℚ) + X ^ 2) * OMA.S_oeis_a049425.series =
      OMA.S_oeis_a049425.series + 2 * (X * OMA.S_oeis_a049425.series) +
        X * (X * OMA.S_oeis_a049425.series) := by
    ring
  rw [hrhs, map_add, map_add, coeff_ofNat_mul, coeff_succ_X_mul,
    coeff_succ_X_mul, coeff_succ_X_mul] at hcoeff
  have hmul := congrArg (((n + 2).factorial : ℚ) * ·) hcoeff
  have hf (m : ℕ) : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have ha0 : OMA.S_oeis_a049425.a n = (n.factorial : ℚ) * coeff n OMA.S_oeis_a049425.series := rfl
  have ha1 : OMA.S_oeis_a049425.a (n + 1) =
      ((n + 1).factorial : ℚ) * coeff (n + 1) OMA.S_oeis_a049425.series := rfl
  have ha2 : OMA.S_oeis_a049425.a (n + 2) =
      ((n + 2).factorial : ℚ) * coeff (n + 2) OMA.S_oeis_a049425.series := rfl
  have ha3 : OMA.S_oeis_a049425.a (n + 3) =
      ((n + 3).factorial : ℚ) * coeff (n + 3) OMA.S_oeis_a049425.series := rfl
  rw [ha0, ha1, ha2, ha3, hf (n + 2), hf (n + 1), hf n]
  rw [hf (n + 1), hf n] at hmul
  push_cast at hmul ⊢
  linear_combination hmul
