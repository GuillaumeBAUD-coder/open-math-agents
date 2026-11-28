import FormalConjectures.OEIS.«158110»

/-! The linear coefficient of the exponential comes only from its linear term. -/

-- Original proof by @philipsaint.
open PowerSeries OeisA158110

theorem OMA.solution : type_of% @OeisA158110.a_1 := by
  have hz : constantCoeff (logSeries 2 3) = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp [logSeries, coeff_mk]
  rw [a, coeff_subst' (HasSubst.of_constantCoeff_zero' hz), finsum_eq_single _ 1]
  · norm_num [coeff_exp, logSeries, coeff_mk]
  · intro k hk
    cases k with
    | zero => simp
    | succ k =>
      have hd := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hz) (k + 1)
      rw [(X_pow_dvd_iff.mp hd) 1 (by omega), smul_zero]
