import FormalConjectures.OEIS.«181076»

-- Problem: Hanna's exponential series for $\binom{n+k-1}{k}^{n}$ — a 0
-- Upstream: formal-conjectures FormalConjectures/OEIS/181076.lean:52 (declaration OeisA181076.a_0)
-- Credit: @YourFriendPollux (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open PowerSeries

theorem OMA.solution : type_of% @OeisA181076.a_0 := by
  rw [OeisA181076.a, OeisA181076.hannaExp, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.constantCoeff_eq]
  rw [constantCoeff_subst (HasSubst.of_constantCoeff_zero' (by simp [OeisA181076.hannaLog]))]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    have hL : MvPowerSeries.constantCoeff
        (OeisA181076.hannaLog fun n k => ((n + k - 1).choose k : ℤ) ^ n) = 0 := by
      unfold OeisA181076.hannaLog
      rw [← PowerSeries.constantCoeff_eq, PowerSeries.constantCoeff_mk]
      simp
    rw [map_pow, hL, zero_pow hd, smul_zero]
