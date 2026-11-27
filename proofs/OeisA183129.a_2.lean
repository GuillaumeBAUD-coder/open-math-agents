import FormalConjectures.OEIS.«183129»

-- Problem: Hanna's exponential series for $\binom{n+k-1}{k}^{k^2+k}$ — a 2
-- Upstream: formal-conjectures FormalConjectures/OEIS/183129.lean:60 (declaration OeisA183129.a_2)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Hanna

open PowerSeries

variable {L : ℚ⟦X⟧}

lemma high (h0 : coeff 0 L = 0) (m d : ℕ) (hd : m < d) : coeff m (L ^ d) = 0 := by
  have hX : (X : ℚ⟦X⟧) ∣ L := by rw [X_dvd_iff]; simpa using h0
  have h := pow_dvd_pow_of_dvd hX d
  rw [X_pow_dvd_iff] at h
  exact h m hd

lemma key (h0 : coeff 0 L = 0) (m : ℕ) :
    coeff m (subst L (exp ℚ))
      = ∑ d ∈ Finset.range (m + 1), coeff d (exp ℚ) • coeff m (L ^ d) := by
  have hs : HasSubst L := HasSubst.of_constantCoeff_zero' (by simpa using h0)
  rw [coeff_subst' hs, finsum_eq_sum_of_support_subset]
  intro d hd
  simp only [Function.mem_support] at hd
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hd (by rw [high h0 m d (by omega), smul_zero])

lemma c22 (h0 : coeff 0 L = 0) : coeff 2 (L ^ 2) = coeff 1 L ^ 2 := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, h0]
  ring

lemma E2 (h0 : coeff 0 L = 0) :
    coeff 2 (subst L (exp ℚ)) = coeff 2 L + coeff 1 L ^ 2 / 2 := by
  rw [key h0]
  simp [Finset.sum_range_succ, coeff_exp, c22 h0, Nat.factorial]
  ring

end OMA.Hanna

open PowerSeries OeisA183129 in
theorem OMA.solution : type_of% @OeisA183129.a_2 := by
  show coeff 2 (subst _ (exp ℚ)) = _
  refine (OMA.Hanna.E2 ?_).trans ?_
  · simp [hannaLog, coeff_mk]
  · simp [hannaLog, coeff_mk, Finset.sum_Icc_succ_top] <;> norm_num [Nat.choose]
