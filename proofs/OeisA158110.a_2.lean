import FormalConjectures.OEIS.«158110»

open PowerSeries

/-- `logSeries 2 3` with its factor of `X` removed. -/
noncomputable def OMA.shifted : ℚ⟦X⟧ :=
  mk fun n => (2 : ℚ) ^ ((n + 1) ^ 3) / ((n + 1 : ℕ) : ℚ)

theorem OMA.logSeries_eq : OeisA158110.logSeries 2 3 = X * OMA.shifted := by
  ext n
  cases n with
  | zero => simp [OeisA158110.logSeries, OMA.shifted]
  | succ n =>
    rw [add_comm n 1, ← pow_one (X : ℚ⟦X⟧), coeff_X_pow_mul']
    simp [OeisA158110.logSeries, OMA.shifted, add_comm]

theorem OMA.solution : type_of% @OeisA158110.a_2 := by
  have h : constantCoeff (OeisA158110.logSeries 2 3) = 0 := by
    simp [OeisA158110.logSeries, constantCoeff_mk]
  have hc : ∀ d : ℕ, coeff 2 (OeisA158110.logSeries 2 3 ^ d) =
      if d ≤ 2 then coeff (2 - d) (OMA.shifted ^ d) else 0 := by
    intro d
    rw [OMA.logSeries_eq, mul_pow, coeff_X_pow_mul']
  rw [OeisA158110.a, coeff_subst' (HasSubst.of_constantCoeff_zero' h),
    finsum_eq_sum_of_support_subset (s := Finset.range 3)]
  · simp only [hc, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [coeff_exp, OMA.shifted, pow_two, coeff_mul]
    norm_num
  · intro d hd
    rw [Function.mem_support] at hd
    by_contra hlt
    apply hd
    have : ¬ d ≤ 2 := by
      intro hle
      exact hlt (Finset.mem_range.mpr (by omega))
    rw [hc, if_neg this, smul_zero]
