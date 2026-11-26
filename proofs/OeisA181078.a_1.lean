import FormalConjectures.OEIS.«181078»

-- Problem: Hanna's exponential series for $\binom{n+k-1}{k}^{n+k-1}$ — a 1
-- Upstream: formal-conjectures FormalConjectures/OEIS/181078.lean:56 (declaration OeisA181078.a_1)
-- Credit: @eitanteperman (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open PowerSeries

/-- Coefficients of a substitution into a series with zero constant term: only finitely many
powers contribute, since X ^ d divides L ^ d. -/
lemma OMA.coeff_subst_eq_sum (L f : ℚ⟦X⟧) (hL : constantCoeff L = 0) (e : ℕ) :
    coeff e (subst L f) = ∑ d ∈ Finset.range (e + 1), coeff d f * coeff e (L ^ d) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero hL)]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (e + 1))]
  · simp only [smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support, ne_eq, Finset.coe_range, Set.mem_Iio] at hd ⊢
    by_contra h
    apply hd
    have hX : X ^ d ∣ L ^ d := pow_dvd_pow_of_dvd (X_dvd_iff.2 hL) d
    rw [X_pow_dvd_iff] at hX
    rw [hX e (by omega), smul_zero]

lemma OMA.coeff_one_subst (L f : ℚ⟦X⟧) (hL : constantCoeff L = 0) :
    coeff 1 (subst L f) = coeff 1 f * coeff 1 L := by
  rw [OMA.coeff_subst_eq_sum L f hL]
  simp [Finset.sum_range_succ, coeff_one]

theorem OMA.solution : type_of% @OeisA181078.a_1 := by
  unfold OeisA181078.a OeisA181078.hannaExp
  have hL : constantCoeff (OeisA181078.hannaLog
      fun n k => ((n + k - 1).choose k : ℤ) ^ (n + k - 1)) = 0 := by
    simp [OeisA181078.hannaLog, ← coeff_zero_eq_constantCoeff_apply]
  rw [OMA.coeff_one_subst _ _ hL]
  simp [OeisA181078.hannaLog, coeff_exp]
