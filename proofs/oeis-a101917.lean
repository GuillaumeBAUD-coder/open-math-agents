import OMAStatements.S_oeis_a101917

open OMA.S_oeis_a101917 PowerSeries

/-! The degree-57 coefficient contradicts Stephan's proposed identity. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a101917.main) := by
  intro h
  have h56 : coeff 57 (series * X) = coeff 56 series := by
    simpa only [pow_one] using coeff_mul_X_pow series 1 56
  have h50 : coeff 57 (series * X^7) = coeff 50 series :=
    coeff_mul_X_pow series 7 50
  have hc := congrArg (coeff 57) h
  simp only [mul_add, mul_one, map_add, h56, h50, coeff_one, coeff_X_pow] at hc
  have obstruction : a 57 + a 56 + a 50 ≠ 0 := by decide +kernel
  have hne0 : (57 : ℕ) ≠ 0 := by decide
  have hne7 : (57 : ℕ) ≠ 7 := by decide
  exact obstruction (by simpa only [series, coeff_mk, if_neg hne0, if_neg hne7, add_zero] using hc)
