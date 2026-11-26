import FormalConjectures.OEIS.«181078»

-- Problem: Hanna's exponential series for $\binom{n+k-1}{k}^{n+k-1}$ — a 2
-- Upstream: formal-conjectures FormalConjectures/OEIS/181078.lean:60 (declaration OeisA181078.a_2)
-- Credit: @Slayzkami (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.A181078

open PowerSeries OeisA181078

noncomputable abbrev L : ℚ⟦X⟧ := hannaLog fun n k => ((n + k - 1).choose k : ℤ) ^ (n + k - 1)

lemma L0 : coeff 0 L = 0 := by
  simp [L, hannaLog, coeff_mk]

lemma L1 : coeff 1 L = 1 := by
  simp [L, hannaLog, coeff_mk]

lemma L2 : coeff 2 L = 3 / 2 := by
  simp [L, hannaLog, coeff_mk, Finset.sum_Icc_succ_top]
  norm_num

lemma hX : (X : ℚ⟦X⟧) ∣ L := by
  rw [X_dvd_iff]
  simpa using L0

lemma L_sq : coeff 2 (L ^ 2) = 1 := by
  rw [pow_two, coeff_mul, Finset.Nat.antidiagonal_succ_succ']
  simp [L0, L1, L2]

lemma high (d : ℕ) (hd : 3 ≤ d) : coeff 2 (L ^ d) = 0 := by
  have h : (X : ℚ⟦X⟧) ^ d ∣ L ^ d := pow_dvd_pow_of_dvd hX d
  rw [X_pow_dvd_iff] at h
  exact h 2 (by omega)

end OMA.A181078

open PowerSeries OMA.A181078 in
theorem OMA.solution : type_of% @OeisA181078.a_2 := by
  have hs : HasSubst L := HasSubst.of_constantCoeff_zero' (by simpa using L0)
  show coeff 2 (subst L (exp ℚ)) = 2
  rw [coeff_subst' hs]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 3)]
  · simp [Finset.sum_range_succ, coeff_exp, L_sq, L2]
    norm_num
  · intro d hd
    simp only [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hd (by rw [high d (by omega), smul_zero])
