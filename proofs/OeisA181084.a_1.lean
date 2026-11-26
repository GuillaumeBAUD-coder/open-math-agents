import FormalConjectures.OEIS.«181084»

namespace OMA.A181084_a1

open PowerSeries OeisA181084

noncomputable abbrev L : ℚ⟦X⟧ := hannaLog fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k + 1) else 0

lemma L0 : coeff 0 L = 0 := by
  simp [L, hannaLog, coeff_mk]

lemma L1 : coeff 1 L = 1 := by
  simp [L, hannaLog, coeff_mk]

lemma hX : (X : ℚ⟦X⟧) ∣ L := by
  rw [X_dvd_iff]
  simpa using L0

lemma low (d k : ℕ) (hd : k < d) : coeff k (L ^ d) = 0 := by
  have h : (X : ℚ⟦X⟧) ^ d ∣ L ^ d := pow_dvd_pow_of_dvd hX d
  rw [X_pow_dvd_iff] at h
  exact h k hd

end OMA.A181084_a1

open PowerSeries OeisA181084 OMA.A181084_a1 in
theorem OMA.solution : type_of% @OeisA181084.a_1 := by
  have hs : HasSubst L := HasSubst.of_constantCoeff_zero' (by simpa using L0)
  show coeff 1 (subst L (exp ℚ)) = 1
  rw [coeff_subst' hs]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (1 + 1))]
  · simp [Finset.sum_range_succ, coeff_exp, L1]
  · intro d hd
    simp only [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hd (by rw [low d 1 (by omega), smul_zero])
