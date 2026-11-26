import FormalConjectures.OEIS.«181082»

-- Problem: Hanna's exponential series for $\binom{n}{k}^{n+k}$ — a 4
-- Upstream: formal-conjectures FormalConjectures/OEIS/181082.lean:68 (declaration OeisA181082.a_4)
-- Credit: @jlgmaarav (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open PowerSeries

theorem OMA.solution : type_of% @OeisA181082.a_4 := by
  -- Every Hanna logarithm has zero constant term.
  have hL : ∀ f : ℕ → ℕ → ℤ, constantCoeff (OeisA181082.hannaLog f) = 0 := by
    intro f
    simp [OeisA181082.hannaLog]
  have h1 : Finset.Icc 1 1 = {1} := by decide
  have h2 : Finset.Icc 1 2 = {1, 2} := by decide
  have h3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have h4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  -- Expand [x^4] exp(L) into finitely many products of coefficients of L and evaluate them.
  rw [OeisA181082.a, OeisA181082.hannaExp, coeff_subst_exp_eq_sum (hL _)]
  simp [Finset.sum_range_succ, pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ,
    OeisA181082.hannaLog, coeff_exp, h1, h2, h3, h4]
  try norm_num [Nat.choose]
