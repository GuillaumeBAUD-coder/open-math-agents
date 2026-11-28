import FormalConjectures.OEIS.«183128»

/-! The first-coefficient formula for powers eliminates every substitution term except the linear one. -/

open OeisA183128 PowerSeries in
theorem OMA.solution : type_of% @OeisA183128.a_1 := by
  change coeff 1 (subst _ (exp ℚ)) = 1
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' (by simp [hannaLog]))]
  rw [finsum_eq_single _ 1]
  · simp [coeff_exp, hannaLog, coeff_mk]
  · intro d hd
    cases d with
    | zero => simp
    | succ d =>
      have : d ≠ 0 := by omega
      simp [coeff_one_pow, hannaLog, this]
