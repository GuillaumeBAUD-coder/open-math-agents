import FormalConjectures.OEIS.«158110»

/-! Only the linear and quadratic terms of the exponential contribute to the quadratic coefficient. -/

-- Original proof by @philipsaint.
open PowerSeries OeisA158110

theorem OMA.solution : type_of% @OeisA158110.a_2 := by
  let L := logSeries 2 3
  have hz : coeff 0 L = 0 := by simp [L, logSeries, coeff_mk]
  have hX : (X : ℚ⟦X⟧) ∣ L := X_dvd_iff.mpr (by simpa using hz)
  have hsq : coeff 2 (L ^ 2) = coeff 1 L ^ 2 := by
    rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_range_succ, hz, pow_two]
  change coeff 2 (subst L (exp ℚ)) = 130
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' (by simpa using hz)),
    finsum_eq_sum_of_support_subset (s := Finset.range 3)]
  · simp only [Finset.sum_range_succ, pow_one, hsq]
    norm_num [coeff_exp, L, logSeries, coeff_mk, Nat.factorial]
  · intro d hd
    by_contra h
    simp only [Finset.coe_range, Set.mem_Iio] at h
    apply hd
    change _ • coeff 2 (L ^ d) = 0
    rw [X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hX d) 2 (by omega), smul_zero]
