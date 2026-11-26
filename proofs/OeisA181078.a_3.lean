import FormalConjectures.OEIS.«181078»

/-! Differentiating the exponential composition expresses each coefficient in terms of
earlier coefficients and the coefficients of Hanna's logarithm. -/

open OeisA181078 PowerSeries in
theorem OMA.solution : type_of% @OeisA181078.a_3 := by
  let L : ℚ⟦X⟧ := hannaLog fun n k => ((n + k - 1).choose k : ℤ) ^ (n + k - 1)
  let S := (exp ℚ).subst L
  have h0 : constantCoeff L = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp [L, hannaLog, coeff_mk]
  have hs : HasSubst L := HasSubst.of_constantCoeff_zero' h0
  have hS0 : coeff 0 S = 1 := by
    change coeff 0 ((exp ℚ).subst L) = 1
    rw [coeff_subst' hs, finsum_eq_single _ 0]
    · simp [coeff_exp]
    · intro d hd
      simp [coeff_zero_eq_constantCoeff, map_pow, h0, zero_pow hd]
  have hL1 : coeff 1 L = 1 := by simp [L, hannaLog, coeff_mk]
  have hL2 : coeff 2 L = 3 / 2 := by
    simp [L, hannaLog, coeff_mk, Finset.sum_Icc_succ_top] <;> norm_num
  have hL3 : coeff 3 L = 10 / 3 := by
    norm_num [L, hannaLog, coeff_mk, Finset.sum_Icc_succ_top, Nat.choose]
  have differential : derivative ℚ S = S * derivative ℚ L := by
    dsimp only [S]
    rw [derivative_subst hs, derivative_exp]
  have recurrence (n : ℕ) : coeff (n + 1) S * ((n : ℚ) + 1) =
      ∑ j ∈ Finset.range (n + 1),
        coeff j S * (coeff (n - j + 1) L * ((n - j : ℕ) + 1 : ℚ)) := by
    rw [← coeff_derivative, differential, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_derivative, Nat.succ_eq_add_one]
  have hS1 := recurrence 0
  norm_num [Finset.sum_range_succ, hS0, hL1] at hS1
  have hS2 := recurrence 1
  norm_num [Finset.sum_range_succ, hS0, hS1, hL1, hL2] at hS2
  change coeff 3 S = 5
  have hS3 := recurrence 2
  norm_num [Finset.sum_range_succ, hS0, hS1, hL1, hL2, hL3] at hS3
  linarith
