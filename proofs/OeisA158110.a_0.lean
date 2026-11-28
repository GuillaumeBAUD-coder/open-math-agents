import FormalConjectures.OEIS.«158110»

/-! Only the constant exponential term contributes. -/
open PowerSeries OeisA158110 in
theorem OMA.solution : type_of% @OeisA158110.a_0 := by
  unfold a
  rw [coeff_subst' (.of_constantCoeff_zero' (by simp [logSeries])), finsum_eq_single _ 0]
  · simp [coeff_exp]
  · intro i hi
    simp [coeff_zero_eq_constantCoeff_apply, logSeries, hi]
