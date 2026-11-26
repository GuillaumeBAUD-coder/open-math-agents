import FormalConjectures.OEIS.«181076»

namespace OMA.A181076_a1

open PowerSeries OeisA181076

noncomputable abbrev L : ℚ⟦X⟧ := hannaLog fun n k => ((n + k - 1).choose k : ℤ) ^ n

lemma L0 : coeff 0 L = 0 := by
  simp [L, hannaLog, coeff_mk]

lemma L1 : coeff 1 L = 1 := by
  simp [L, hannaLog, coeff_mk]

lemma hX : (X : ℚ⟦X⟧) ∣ L := by
  rw [X_dvd_iff]
  simpa using L0

lemma high (d : ℕ) (hd : 2 ≤ d) : coeff 1 (L ^ d) = 0 := by
  have h : (X : ℚ⟦X⟧) ^ d ∣ L ^ d := pow_dvd_pow_of_dvd hX d
  rw [X_pow_dvd_iff] at h
  exact h 1 (by omega)

end OMA.A181076_a1

open PowerSeries OMA.A181076_a1 in
theorem OMA.solution : type_of% @OeisA181076.a_1 := by
  have hs : HasSubst L := HasSubst.of_constantCoeff_zero' (by simpa using L0)
  show coeff 1 (subst L (exp ℚ)) = 1
  rw [coeff_subst' hs]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, coeff_exp, L1]
  · intro d hd
    simp only [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hd (by rw [high d (by omega), smul_zero])
