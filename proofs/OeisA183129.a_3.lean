import FormalConjectures.OEIS.«183129»

open PowerSeries OeisA183129

theorem OMA.solution : type_of% @OeisA183129.a_3 := by
  have hg : (hannaLog fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k)).constantCoeff = 0 := by
    simp [hannaLog, ← coeff_zero_eq_constantCoeff_apply]
  unfold a hannaExp
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg), finsum_eq_sum_of_support_subset (s := .range 4)]
  · norm_num [Finset.sum_range_succ, coeff_exp, pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ,
      hannaLog, coeff_mk, Finset.sum_Icc_succ_top, Nat.factorial]
  intro d hd
  by_contra h
  exact hd (smul_eq_zero_of_right _ (coeff_of_lt_order _ ((by exact_mod_cast (by simp at h; omega : 3 < d) : (3 : ℕ∞) < d).trans_le
    (le_order_pow_of_constantCoeff_eq_zero d hg))))
