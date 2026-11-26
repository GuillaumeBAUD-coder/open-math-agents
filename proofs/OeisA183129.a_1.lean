import FormalConjectures.OEIS.«183129»

open PowerSeries

/-- A power series with zero constant term, with its factor of `X` removed. -/
noncomputable def OMA.shift (L : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  mk fun n => coeff (n + 1) L

theorem OMA.eq_X_mul_shift (L : ℚ⟦X⟧) (h : constantCoeff L = 0) : L = X * OMA.shift L := by
  ext n
  cases n with
  | zero => simpa using h
  | succ n =>
    rw [add_comm n 1, ← pow_one (X : ℚ⟦X⟧), coeff_X_pow_mul']
    simp [OMA.shift, add_comm]

theorem OMA.solution : type_of% @OeisA183129.a_1 := by
  have h : constantCoeff
      (OeisA183129.hannaLog fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k)) = 0 := by
    simp [OeisA183129.hannaLog, constantCoeff_mk]
  have hc : ∀ d : ℕ, coeff 1
      ((OeisA183129.hannaLog fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k)) ^ d) =
      if d ≤ 1 then coeff (1 - d)
        (OMA.shift (OeisA183129.hannaLog fun n k =>
          ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k)) ^ d) else 0 := by
    intro d
    conv_lhs => rw [OMA.eq_X_mul_shift _ h, mul_pow, coeff_X_pow_mul']
  rw [OeisA183129.a, OeisA183129.hannaExp, coeff_subst' (HasSubst.of_constantCoeff_zero' h),
    finsum_eq_sum_of_support_subset (s := Finset.range 2)]
  · simp only [hc, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [coeff_exp, OMA.shift, OeisA183129.hannaLog]
  · intro d hd
    rw [Function.mem_support] at hd
    by_contra hlt
    apply hd
    have : ¬ d ≤ 1 := by
      intro hle
      exact hlt (Finset.mem_range.mpr (by omega))
    rw [hc, if_neg this, smul_zero]
