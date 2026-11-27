import FormalConjectures.OEIS.«158110»

-- Problem: Exponentials of $\sum_{n \ge 1} q^{n^m} x^n / n$ — a 1
-- Upstream: formal-conjectures FormalConjectures/OEIS/158110.lean:57 (declaration OeisA158110.a_1)
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

lemma E1 (h0 : coeff 0 L = 0) : coeff 1 (subst L (exp ℚ)) = coeff 1 L := by
  rw [key h0]
  simp [Finset.sum_range_succ, coeff_exp]

end OMA.Hanna

open PowerSeries OeisA158110 in
theorem OMA.solution : type_of% @OeisA158110.a_1 := by
  show coeff 1 (subst _ (exp ℚ)) = _
  refine (OMA.Hanna.E1 ?_).trans ?_
  · simp [logSeries, coeff_mk]
  · simp [logSeries, coeff_mk, Finset.sum_Icc_succ_top] <;> norm_num [Nat.choose]
