import FormalConjectures.OEIS.«183129»

open PowerSeries

theorem OMA.solution : type_of% @OeisA183129.a_0 := by
  rw [OeisA183129.a, OeisA183129.hannaExp, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.constantCoeff_eq]
  rw [constantCoeff_subst (HasSubst.of_constantCoeff_zero' (by simp [OeisA183129.hannaLog]))]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    have hL : MvPowerSeries.constantCoeff
        (OeisA183129.hannaLog fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k)) = 0 := by
      unfold OeisA183129.hannaLog
      rw [← PowerSeries.constantCoeff_eq, PowerSeries.constantCoeff_mk]
      simp
    rw [map_pow, hL, zero_pow hd, smul_zero]
