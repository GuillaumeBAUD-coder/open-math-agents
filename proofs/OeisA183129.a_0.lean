import FormalConjectures.OEIS.«183129»

open OeisA183129 PowerSeries
theorem OMA.solution : type_of% @OeisA183129.a_0 := by
  unfold a hannaExp
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' (by simp [hannaLog, constantCoeff_mk])),
    finsum_eq_single _ 0]
  · simp [coeff_exp]
  · intro i hi
    simp [coeff_zero_eq_constantCoeff_apply, hannaLog, constantCoeff_mk, hi]
