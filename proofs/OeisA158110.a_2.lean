import FormalConjectures.OEIS.«158110»

open OeisA158110 PowerSeries

theorem OMA.solution : type_of% @OeisA158110.a_2 := by
  have h : (X : ℚ⟦X⟧) ∣ logSeries 2 3 := X_dvd_iff.mpr (by simp [logSeries])
  rw [a, coeff_subst' (.of_constantCoeff_zero' (X_dvd_iff.mp h))]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range 3)]
  · norm_num [Finset.sum_range_succ, coeff_exp, pow_two, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, logSeries, coeff_mk, Nat.factorial]
  · intro d hd
    by_contra hn
    simp at hn
    exact hd (smul_eq_zero_of_right _ (X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd h d) 2 (by omega)))
