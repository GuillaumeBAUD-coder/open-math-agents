import OMAStatements.S_oeis_a267881

/-!
# OEIS A267881: Barker's conjectures for Rule 233: the conjectured package is inconsistent

The generating-function identity determines the sequence: comparing the coefficients of
`X ^ 3, X ^ 4, X ^ 5` gives `a 3 - 2 a 2 + a 1 = 0`, `a 4 - 2 a 3 + a 2 = 0` and
`a 5 - 2 a 4 + a 3 = -1`. The claimed recurrence at `n = 5` says `a 5 - 2 a 4 + a 3 = 0`.
-/

open OMA.S_oeis_a267881 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267881.main) := by
  rintro ⟨hr, hgf⟩
  have el : ∀ S : PowerSeries ℤ, S * (1 - X) ^ 2 =
      C (1 : ℤ) * (S * X ^ 0) + C (-2 : ℤ) * (S * X ^ 1) + C (1 : ℤ) * (S * X ^ 2) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (1 - 2 * X + 4 * X ^ 2 - X ^ 5 : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 1 : PowerSeries ℤ) * C (-2 : ℤ) +
        (X ^ 2 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (-1 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  have h := congrArg (PowerSeries.coeff 5) hgf
  simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
  have h5 := hr 5 (by norm_num)
  norm_num at h h5
  linarith
