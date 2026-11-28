import FormalConjectures.OEIS.«183128»

/-! Expand the exponential of the series abstractly, then evaluate its first coefficients. -/

open PowerSeries OeisA183128

theorem OMA.solution : type_of% @OeisA183128.a_4 := by
  set L := hannaLog fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + 1)
  have h0 : constantCoeff L = 0 := by simp [L, hannaLog]
  show coeff 4 (subst L (exp ℚ)) = 131
  rw [coeff_subst' (.of_constantCoeff_zero' h0), finsum_eq_sum_of_support_subset _
    (s := Finset.range 5) fun d hd => by_contra fun h => hd <| by
      simp [X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 h0) d) 4 (by simp at h; omega)]]
  simp [Finset.sum_range_succ, pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    coeff_exp, Nat.factorial, h0]
  simp [L, hannaLog, Finset.sum_Icc_succ_top]
  norm_num [Nat.choose]
