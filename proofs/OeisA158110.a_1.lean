import FormalConjectures.OEIS.«158110»

namespace OMA.A158110_a1

open PowerSeries OeisA158110

lemma L0 : coeff 0 (logSeries 2 3) = 0 := by
  simp [logSeries, coeff_mk]

lemma L1 : coeff 1 (logSeries 2 3) = 2 := by
  simp [logSeries, coeff_mk]

lemma hX : (X : ℚ⟦X⟧) ∣ logSeries 2 3 := by
  rw [X_dvd_iff]
  simpa using L0

lemma high (d : ℕ) (hd : 2 ≤ d) : coeff 1 (logSeries 2 3 ^ d) = 0 := by
  have h : (X : ℚ⟦X⟧) ^ d ∣ logSeries 2 3 ^ d := pow_dvd_pow_of_dvd hX d
  rw [X_pow_dvd_iff] at h
  exact h 1 (by omega)

end OMA.A158110_a1

open PowerSeries OeisA158110 OMA.A158110_a1 in
theorem OMA.solution : type_of% @OeisA158110.a_1 := by
  have hs : HasSubst (logSeries 2 3) := HasSubst.of_constantCoeff_zero' (by simpa using L0)
  show coeff 1 (subst (logSeries 2 3) (exp ℚ)) = 2
  rw [coeff_subst' hs]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, coeff_exp, L1]
  · intro d hd
    simp only [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hd (by rw [high d (by omega), smul_zero])
