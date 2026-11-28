import OMAStatements.S_oeis_a266794

/-!
# OEIS A266794: Barker's conjectures are inconsistent

The coefficient of `X ^ 8` of the generating-function identity reads
`a 8 - 2 a 6 + a 4 = 1`, while the claimed recurrence at `n = 8` says it is 0.
-/

open OMA.S_oeis_a266794 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a266794.main) := by
  rintro ⟨h0, h1, h2⟩
  have el : ∀ S : PowerSeries ℤ, S * ((1 - X) ^ 2 * (1 + X) ^ 2) =
      C (1 : ℤ) * (S * X ^ 0) +
        C (-2 : ℤ) * (S * X ^ 2) +
        C (1 : ℤ) * (S * X ^ 4) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (X * (1 + 3 * X - X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7) : PowerSeries ℤ) =
      (X ^ 1 : PowerSeries ℤ) * C (1 : ℤ) +
        (X ^ 2 : PowerSeries ℤ) * C (3 : ℤ) +
        (X ^ 4 : PowerSeries ℤ) * C (-1 : ℤ) +
        (X ^ 5 : PowerSeries ℤ) * C (1 : ℤ) +
        (X ^ 6 : PowerSeries ℤ) * C (1 : ℤ) +
        (X ^ 7 : PowerSeries ℤ) * C (-2 : ℤ) +
        (X ^ 8 : PowerSeries ℤ) * C (1 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at h2
  have h := congrArg (PowerSeries.coeff 8) h2
  simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
  have hm := h1 8 (by norm_num)
  simp only [Nat.reduceSub] at hm
  simp only [Nat.reduceLeDiff, Nat.reduceSub, if_true, if_false, Nat.reduceEqDiff, mul_one, add_zero] at h
  linarith
