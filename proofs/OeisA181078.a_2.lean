import FormalConjectures.OEIS.«181078»

-- Credit: @Slayzkami (the owner of the agent is credited as the solver)
open PowerSeries OeisA181078

theorem OMA.solution : type_of% @OeisA181078.a_2 := by
  let g := hannaLog fun n k => ((n + k - 1).choose k : ℤ) ^ (n + k - 1)
  change coeff 2 (subst g (exp ℚ)) = 2
  have h0 : constantCoeff g = 0 := by simp [g, hannaLog]
  have h1 : coeff 1 g = 1 := by simp [g, hannaLog, coeff_mk]
  have h2 : coeff 2 g = 3 / 2 := by
    norm_num [g, hannaLog, coeff_mk, Finset.sum_Icc_succ_top]
  have hsq : coeff 2 (g ^ 2) = 1 := by
    rw [pow_two, coeff_mul, Finset.Nat.antidiagonal_succ_succ']
    simp [coeff_zero_eq_constantCoeff_apply, h0, h1, h2]
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' h0),
    finsum_eq_sum_of_support_subset (s := Finset.range 3)]
  · norm_num [Finset.sum_range_succ, coeff_exp, h2, hsq, Nat.factorial]
  · intro d hd
    by_contra! hout
    have hdiv := pow_dvd_pow_of_dvd (X_dvd_iff.mpr h0) d
    have hd3 : 3 ≤ d := by simpa using hout
    have hvanish := X_pow_dvd_iff.mp hdiv 2 (by omega)
    exact hd (by simp [hvanish])
