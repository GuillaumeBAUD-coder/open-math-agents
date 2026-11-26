import FormalConjectures.OEIS.«158110»

-- Problem: Exponentials of $\sum_{n \ge 1} q^{n^m} x^n / n$ — a 0
-- Upstream: formal-conjectures FormalConjectures/OEIS/158110.lean:53 (declaration OeisA158110.a_0)
-- Credit: @YourFriendPollux (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open PowerSeries

theorem OMA.solution : type_of% @OeisA158110.a_0 := by
  rw [OeisA158110.a, PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_eq]
  rw [constantCoeff_subst (HasSubst.of_constantCoeff_zero' (by simp [OeisA158110.logSeries]))]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    have hL : MvPowerSeries.constantCoeff (OeisA158110.logSeries 2 3) = 0 := by
      unfold OeisA158110.logSeries
      rw [← PowerSeries.constantCoeff_eq, PowerSeries.constantCoeff_mk]
      simp
    rw [map_pow, hL, zero_pow hd, smul_zero]
