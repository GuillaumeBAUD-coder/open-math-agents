import FormalConjectures.OEIS.«183128»

-- Problem: Hanna's exponential series for $\binom{n+k-1}{k}^{k^2+1}$ — a 4
-- Upstream: formal-conjectures FormalConjectures/OEIS/183128.lean:68 (declaration OeisA183128.a_4)
-- Credit: @jlgmaarav (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open PowerSeries

theorem OMA.solution : type_of% @OeisA183128.a_4 := by
  -- Every Hanna logarithm has zero constant term.
  have hL : ∀ f : ℕ → ℕ → ℤ, constantCoeff (OeisA183128.hannaLog f) = 0 := by
    intro f
    simp [OeisA183128.hannaLog]
  have h1 : Finset.Icc 1 1 = {1} := by decide
  have h2 : Finset.Icc 1 2 = {1, 2} := by decide
  have h3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have h4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  -- Expand [x^4] exp(L) into finitely many products of coefficients of L and evaluate them.
  rw [OeisA183128.a, OeisA183128.hannaExp, coeff_subst_exp_eq_sum (hL _)]
  simp [Finset.sum_range_succ, pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ,
    OeisA183128.hannaLog, coeff_exp, h1, h2, h3, h4]
  try norm_num [Nat.choose]
