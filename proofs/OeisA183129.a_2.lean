import FormalConjectures.OEIS.«183129»

-- Problem: Hanna's exponential series for $\binom{n+k-1}{k}^{k^2+k}$ — a 2
-- Upstream: formal-conjectures FormalConjectures/OEIS/183129.lean:60 (declaration OeisA183129.a_2)
-- Credit: @jlgmaarav (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open PowerSeries

/-- For a series `L` with zero constant term, `[x^m] exp(L)` is a finite sum over `d ≤ m`. -/
lemma coeff_subst_exp_eq_sum {L : ℚ⟦X⟧} (hL : constantCoeff L = 0) (m : ℕ) :
    coeff m (subst L (exp ℚ)) =
      ∑ d ∈ Finset.range (m + 1), coeff d (exp ℚ) * coeff m (L ^ d) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hL),
    finsum_eq_sum_of_support_subset _ (s := Finset.range (m + 1)) ?_]
  · simp [smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hd
    obtain ⟨g, hg⟩ : X ∣ L := X_dvd_iff.mpr hL
    rw [hg, mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]

theorem OMA.solution : type_of% @OeisA183129.a_2 := by
  -- Every Hanna logarithm has zero constant term.
  have hL : ∀ f : ℕ → ℕ → ℤ, constantCoeff (OeisA183129.hannaLog f) = 0 := by
    intro f
    simp [OeisA183129.hannaLog]
  have h1 : Finset.Icc 1 1 = {1} := by decide
  have h2 : Finset.Icc 1 2 = {1, 2} := by decide
  have h3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have h4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  -- Expand [x^2] exp(L) into finitely many products of coefficients of L and evaluate them.
  rw [OeisA183129.a, OeisA183129.hannaExp, coeff_subst_exp_eq_sum (hL _)]
  simp [Finset.sum_range_succ, pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ,
    OeisA183129.hannaLog, coeff_exp, h1, h2, h3, h4]
  try norm_num [Nat.choose]
