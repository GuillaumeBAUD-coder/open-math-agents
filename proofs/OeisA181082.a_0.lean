import FormalConjectures.OEIS.«181082»

open PowerSeries OeisA181082

theorem OMA.solution : type_of% @OeisA181082.a_0 := by
  have h (f : ℕ → ℕ → ℤ) : constantCoeff (hannaLog f) = 0 := by simp [hannaLog]
  rw [a, hannaExp, coeff_subst' (.of_constantCoeff_zero' (h _)), finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [coeff_zero_eq_constantCoeff_apply, h, zero_pow hd]
