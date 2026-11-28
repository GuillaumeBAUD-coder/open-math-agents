import FormalConjectures.OEIS.«181084»

open PowerSeries OeisA181084

theorem OMA.solution : type_of% @OeisA181084.a_3 := by
  have h0 (f) : constantCoeff (hannaLog f) = 0 := by simp [hannaLog]
  rw [a, hannaExp, coeff_subst' (.of_constantCoeff_zero' (h0 _)), finsum_eq_sum_of_support_subset _
    (s := Finset.range 4) fun d hd => by_contra fun h => hd <| by
      simp [X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 (h0 _)) d) 3 (by simp at h; omega)]]
  simp [Finset.sum_range_succ, pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hannaLog, Finset.sum_Icc_succ_top]
  norm_num
