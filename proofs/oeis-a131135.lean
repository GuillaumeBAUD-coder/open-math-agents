import OMAStatements.S_oeis_a131135

-- Problem: A131135: Denominator of (ordinary) expansion of log((x/2-1)/(x-1)).
-- Upstream: formal-conjectures statements/oeis-a131135.lean:0 (declaration OMA.S_oeis_a131135.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: L = logOf F = log(1+X) with G = F - 1 substituted. By the chain rule
-- L' = M(G) * F' with M = 1/(1+X) the derivative of log(1+X), and (1+X) M = 1 gives F M(G) = 1,
-- so L' F = F'. With F (X - 1) = X/2 - 1 this gives L' (X/2 - 1)(X - 1) = 1/2, so the
-- coefficients l(n) of L' satisfy l(0) = 1/2, l(1) = 3/2 l(0), l(n+2) = 3/2 l(n+1) - 1/2 l(n),
-- hence l(n) = 1 - 1/2^(n+1), and the coefficient of x^(n+1) in L is l(n)/(n+1).

namespace R08A131135

open OMA.S_oeis_a131135 PowerSeries

theorem X1_cc : constantCoeff (X - 1 : ℚ⟦X⟧) ≠ 0 := by
  rw [map_sub, constantCoeff_X, map_one]
  norm_num

theorem hF1 : F * (X - 1) = C (1 / 2 : ℚ) * X - 1 := by
  rw [F, mul_assoc, PowerSeries.inv_mul_cancel _ X1_cc, mul_one]

theorem cc_F : constantCoeff F = 1 := by
  have h := congrArg constantCoeff hF1
  simp only [map_mul, map_sub, map_one, constantCoeff_X, constantCoeff_C] at h
  linear_combination -h

theorem hG : HasSubst (F - 1) := by
  apply HasSubst.of_constantCoeff_zero'
  rw [map_sub, cc_F, map_one, sub_self]

theorem hM : (1 + X) * (mk fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)) = (1 : ℚ⟦X⟧) := by
  ext n
  rw [add_mul, one_mul, map_add, coeff_one]
  rcases n with _ | k
  · rw [coeff_zero_X_mul, coeff_mk, pow_zero, map_one, add_zero,
      if_pos (show (0 : ℕ) = 0 from rfl)]
  · rw [coeff_succ_X_mul, coeff_mk, coeff_mk, ← map_add,
      show (-1 : ℚ) ^ (k + 1) + (-1) ^ k = 0 by ring, map_zero,
      if_neg (show ¬ (k + 1 = 0) by omega)]

theorem hS : F * (mk fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)).subst (F - 1) = 1 := by
  have h1 : (1 : ℚ⟦X⟧).subst (F - 1) = (1 : ℚ⟦X⟧) := by
    rw [← coe_substAlgHom hG, map_one]
  have h : ((1 + X) * (mk fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n))).subst (F - 1) =
      (1 : ℚ⟦X⟧).subst (F - 1) := by
    rw [hM]
  rw [subst_mul hG, subst_add hG, subst_X hG, h1] at h
  linear_combination h

theorem hdL : d⁄dX ℚ (logOf F) * F = d⁄dX ℚ F := by
  rw [logOf_eq, derivative_subst hG, deriv_log, map_sub (d⁄dX ℚ) F 1, derivative_one, sub_zero]
  linear_combination (d⁄dX ℚ F) * hS

theorem hdF : d⁄dX ℚ F * (X - 1) + F = C (1 / 2 : ℚ) := by
  have h := congrArg (d⁄dX ℚ) hF1
  simp only [Derivation.leibniz, map_sub, derivative_X, derivative_one, derivative_C,
    smul_eq_mul] at h
  linear_combination h

theorem key : d⁄dX ℚ (logOf F) = C (1 / 2 : ℚ) + C (3 / 2 : ℚ) * (X * d⁄dX ℚ (logOf F)) -
    C (1 / 2 : ℚ) * (X * (X * d⁄dX ℚ (logOf F))) := by
  have hc0 : (C (1 : ℚ) : ℚ⟦X⟧) = 1 := map_one _
  have hc1 : (C (3 / 2 : ℚ) : ℚ⟦X⟧) = C (1 / 2 : ℚ) + C 1 := by
    rw [← map_add]
    norm_num
  have hc2 : (C (1 / 2 : ℚ) : ℚ⟦X⟧) + C (1 / 2 : ℚ) = C 1 := by
    rw [← map_add]
    norm_num
  linear_combination (X - 1) ^ 2 * hdL + (X - 1) * hdF -
    (d⁄dX ℚ (logOf F) * (X - 1) + 1) * hF1 - X * d⁄dX ℚ (logOf F) * hc1 -
    (X * d⁄dX ℚ (logOf F) + 1) * hc0 - hc2

theorem c0 (m : ℕ) : coeff m (d⁄dX ℚ (logOf F)) = coeff m (C (1 / 2 : ℚ)) +
    3 / 2 * coeff m (X * d⁄dX ℚ (logOf F)) - 1 / 2 * coeff m (X * (X * d⁄dX ℚ (logOf F))) := by
  conv_lhs => rw [key]
  rw [map_sub, map_add, coeff_C_mul, coeff_C_mul]

theorem coeff_dL (n : ℕ) : coeff n (d⁄dX ℚ (logOf F)) = 1 - 1 / 2 ^ (n + 1) ∧
    coeff (n + 1) (d⁄dX ℚ (logOf F)) = 1 - 1 / 2 ^ (n + 2) := by
  induction n with
  | zero =>
    have h0 := c0 0
    have h1 := c0 (0 + 1)
    rw [coeff_C, if_pos (show (0 : ℕ) = 0 from rfl), coeff_zero_X_mul, coeff_zero_X_mul] at h0
    rw [coeff_C, if_neg (show ¬ ((0 : ℕ) + 1 = 0) by omega), coeff_succ_X_mul, coeff_succ_X_mul,
      coeff_zero_X_mul] at h1
    have e0 : coeff 0 (d⁄dX ℚ (logOf F)) = 1 / 2 := by
      rw [h0]
      norm_num
    refine ⟨?_, ?_⟩
    · rw [e0]
      norm_num
    · rw [h1, e0]
      norm_num
  | succ k ih =>
    refine ⟨ih.2.trans (by ring), ?_⟩
    have h := c0 (k + 1 + 1)
    rw [coeff_C, if_neg (show ¬ (k + 1 + 1 = 0) by omega), coeff_succ_X_mul, coeff_succ_X_mul,
      coeff_succ_X_mul] at h
    rw [h, ih.1, ih.2]
    ring

theorem coeff_L (m : ℕ) :
    coeff (m + 1) (logOf F) = (1 - 1 / 2 ^ (m + 1)) / ((m : ℚ) + 1) := by
  have h := coeff_derivative (logOf F) m
  rw [(coeff_dL m).1] at h
  have hm : (m : ℚ) + 1 ≠ 0 := by positivity
  rw [eq_div_iff hm]
  exact h.symm

end R08A131135

open OMA.S_oeis_a131135 R08A131135 in
theorem OMA.solution : type_of% @OMA.S_oeis_a131135.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a, coeff_L m, Nat.cast_add_one]
