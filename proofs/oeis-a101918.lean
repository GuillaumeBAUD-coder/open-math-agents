import OMAStatements.S_oeis_a101918

-- Credit: @mjsechrest2
open OMA.S_oeis_a101918 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a101918.main) := by
  intro h
  have h73 := congrArg (coeff (R := ℤ) 73) h
  have e8 : coeff (R := ℤ) 73 (series * X ^ 8) = a 65 := by
    rw [show (73 : ℕ) = 65 + 8 from rfl, coeff_mul_X_pow]; exact coeff_mk _ _
  simp only [mul_add, mul_one, map_add, coeff_succ_mul_X, e8, coeff_one, coeff_X_pow,
    show (73 : ℕ) ≠ 0 by decide, show (73 : ℕ) ≠ 8 by decide, ↓reduceIte, add_zero] at h73
  simp only [series, coeff_mk] at h73
  exact (by decide +kernel : a 73 + a 72 + a 65 ≠ 0) h73
