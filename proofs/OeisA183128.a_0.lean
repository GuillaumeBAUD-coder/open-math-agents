import FormalConjectures.OEIS.«183128»

-- Problem: Hanna's exponential series for $\binom{n+k-1}{k}^{k^2+1}$ — a 0
-- Upstream: formal-conjectures FormalConjectures/OEIS/183128.lean:52 (declaration OeisA183128.a_0)
-- Credit: @jlgmaarav (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @OeisA183128.a_0 := by
  -- The logarithmic series has zero constant term (its coefficient of x^0 is an empty sum).
  have hL : PowerSeries.constantCoeff
      (OeisA183128.hannaLog fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + 1)) = 0 := by
    simp [OeisA183128.hannaLog]
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' hL
  -- [x^0] exp(L) = sum_d [x^d]exp * [x^0] L^d, and only d = 0 survives.
  rw [OeisA183128.a, OeisA183128.hannaExp, PowerSeries.coeff_subst' hS, finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hL, zero_pow hd, smul_zero]
