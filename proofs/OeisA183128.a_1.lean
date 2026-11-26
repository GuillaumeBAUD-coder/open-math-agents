import FormalConjectures.OEIS.«183128»

-- Problem: Hanna's exponential series for $\binom{n+k-1}{k}^{k^2+1}$ — a 1
-- Upstream: formal-conjectures FormalConjectures/OEIS/183128.lean:56 (declaration OeisA183128.a_1)
-- Credit: @avivorly (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open PowerSeries

lemma OMA_coeff_one_pow_eq_zero (L : ℚ⟦X⟧) (hL : constantCoeff L = 0) (d : ℕ) (hd : d ≠ 1) :
    coeff 1 (L ^ d) = 0 := by
  rcases Nat.lt_or_gt_of_ne hd with h | h
  · have : d = 0 := by omega
    subst this
    simp
  · obtain ⟨M, hM⟩ := X_dvd_iff.mpr hL
    rw [hM, mul_pow, coeff_X_pow_mul']
    simp
    omega

theorem OMA.solution : type_of% @OeisA183128.a_1 := by
  unfold OeisA183128.a OeisA183128.hannaExp
  set L := OeisA183128.hannaLog fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + 1) with hLdef
  have hL0 : constantCoeff L = 0 := by
    rw [hLdef, OeisA183128.hannaLog, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    simp
  have hL1 : coeff 1 L = 1 := by
    rw [hLdef, OeisA183128.hannaLog, coeff_mk]
    simp
  have hS : HasSubst L := HasSubst.of_constantCoeff_zero' hL0
  rw [coeff_subst' hS, finsum_eq_single _ 1]
  · simp [hL1, coeff_exp]
  · intro d hd
    rw [OMA_coeff_one_pow_eq_zero L hL0 d hd, smul_zero]
