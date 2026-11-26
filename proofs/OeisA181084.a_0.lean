import FormalConjectures.OEIS.«181084»

open PowerSeries

theorem OMA.hanna_constantCoeff (f : ℕ → ℕ → ℤ) :
    constantCoeff (OeisA181084.hannaExp f) = 1 := by
  have hzero : constantCoeff (OeisA181084.hannaLog f) = 0 := by
    rw [OeisA181084.hannaLog, constantCoeff_mk,
      Finset.Icc_eq_empty (by decide : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty]
  change MvPowerSeries.constantCoeff (subst (OeisA181084.hannaLog f) (exp ℚ)) = 1
  rw [constantCoeff_subst (HasSubst.of_constantCoeff_zero hzero), finsum_eq_single _ 0]
  · simp
  · intro n hn
    change coeff n (exp ℚ) • constantCoeff (OeisA181084.hannaLog f ^ n) = 0
    rw [map_pow, hzero, zero_pow hn, smul_zero]

theorem OMA.solution : type_of% @OeisA181084.a_0 := by
  unfold OeisA181084.a
  rw [coeff_zero_eq_constantCoeff_apply]
  exact OMA.hanna_constantCoeff _
