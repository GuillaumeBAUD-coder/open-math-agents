import FormalConjectures.OEIS.«181082»

open PowerSeries OeisA181082

theorem OMA.solution : type_of% @OeisA181082.a_2 := by
  have hg : constantCoeff (hannaLog fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k) else 0) = 0 := by
    simp [hannaLog]
  unfold a hannaExp
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg), finsum_eq_sum_of_support_subset (s := .range 3)]
  · norm_num [Finset.sum_range_succ, coeff_exp, pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ,
      hannaLog, coeff_mk, Finset.sum_Icc_succ_top]
  intro d hd
  by_contra h
  exact hd (by simp [X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hg) d) 2 (by simp at h; omega)])
