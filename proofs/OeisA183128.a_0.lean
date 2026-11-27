import FormalConjectures.OEIS.«183128»

-- Problem: Hanna's exponential series for $\binom{n+k-1}{k}^{k^2+1}$ — a 0
-- Upstream: formal-conjectures FormalConjectures/OEIS/183128.lean:52 (declaration OeisA183128.a_0)
-- Credit: @jlgmaarav (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open PowerSeries OeisA183128

theorem OMA.solution : type_of% @OeisA183128.a_0 := by
  have h (f : ℕ → ℕ → ℤ) : constantCoeff (hannaLog f) = 0 := by simp [hannaLog]
  rw [a, hannaExp, coeff_subst' (.of_constantCoeff_zero' (h _)), finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [coeff_zero_eq_constantCoeff_apply, h, zero_pow hd]
