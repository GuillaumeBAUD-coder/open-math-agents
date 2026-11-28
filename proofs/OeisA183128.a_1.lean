import FormalConjectures.OEIS.«183128»

/-! Only the linear term survives: the substituted series has zero constant coefficient. -/

open OeisA183128 PowerSeries in
theorem OMA.solution : type_of% @OeisA183128.a_1 := by
  change coeff 1 (subst _ (exp ℚ)) = 1
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' (by simp [hannaLog])), finsum_eq_single _ 1]
  · simp [coeff_exp, hannaLog, coeff_mk]
  · rintro (_ | _ | d) hd <;> simp_all [coeff_one_pow, hannaLog]
