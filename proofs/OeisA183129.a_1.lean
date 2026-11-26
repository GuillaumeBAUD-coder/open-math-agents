import FormalConjectures.OEIS.«183129»

-- Credit: @aspher1

open PowerSeries OeisA183129

-- Uses the X-divisibility coefficient bound employed in the existing
-- proofs/OeisA181078.a_2.lean proof.
theorem OMA.solution : type_of% @OeisA183129.a_1 := by
  let L : PowerSeries ℚ := hannaLog fun n k =>
    ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k)
  have hL0 : PowerSeries.constantCoeff L = 0 := by
    simp [L, hannaLog]
  have hL1 : coeff 1 L = 1 := by
    simp [L, hannaLog, coeff_mk]
  have hX : (X : PowerSeries ℚ) ∣ L := by
    rw [X_dvd_iff]
    exact hL0
  have high (d : ℕ) (hd : 2 ≤ d) : coeff 1 (L ^ d) = 0 := by
    have h := pow_dvd_pow_of_dvd hX d
    rw [X_pow_dvd_iff] at h
    exact h 1 (by omega)
  change coeff 1 (subst L (exp ℚ)) = 1
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hL0)]
  rw [finsum_eq_single _ 1]
  · simp [hL1]
  · intro d hd
    by_cases h0 : d = 0
    · subst d
      simp
    · rw [high d (by omega), smul_zero]
