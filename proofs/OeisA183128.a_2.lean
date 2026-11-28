import FormalConjectures.OEIS.«183128»

/-! Only finitely many powers contribute; evaluate the surviving coefficients directly. -/

open PowerSeries OeisA183128 in
theorem OMA.solution : type_of% @OeisA183128.a_2 := by
  unfold a hannaExp
  rw [coeff_subst' (.of_constantCoeff_zero' (by simp [hannaLog])),
    finsum_eq_sum_of_support_subset (s := Finset.range 3)]
  · norm_num [Finset.sum_range_succ, coeff_exp, pow_succ, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hannaLog,
      Finset.sum_Icc_succ_top, Nat.factorial, Nat.choose]
  · intro d hd
    by_contra h
    apply hd
    apply smul_eq_zero_of_right
    exact X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 (by simp [hannaLog])) d)
      2 (by simp at h; omega)

