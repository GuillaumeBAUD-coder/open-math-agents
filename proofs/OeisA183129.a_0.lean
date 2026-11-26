import FormalConjectures.OEIS.«183129»

-- Problem: Hanna's exponential series for $\binom{n+k-1}{k}^{k^2+k}$ — a 0
-- Upstream: formal-conjectures FormalConjectures/OEIS/183129.lean:52 (declaration OeisA183129.a_0)
-- Credit: @jlgmaarav (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @OeisA183129.a_0 := by
  -- Every Hanna logarithm has zero constant term (its coefficient of x^0 is an empty sum).
  have hL : ∀ f : ℕ → ℕ → ℤ, PowerSeries.constantCoeff (OeisA183129.hannaLog f) = 0 := by
    intro f
    simp [OeisA183129.hannaLog]
  have hS : ∀ f : ℕ → ℕ → ℤ, PowerSeries.HasSubst (OeisA183129.hannaLog f) :=
    fun f => PowerSeries.HasSubst.of_constantCoeff_zero' (hL f)
  -- [x^0] exp(L) = sum_d [x^d]exp * [x^0] L^d, and only d = 0 survives.
  rw [OeisA183129.a, OeisA183129.hannaExp, PowerSeries.coeff_subst' (hS _), finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hL, zero_pow hd, smul_zero]
