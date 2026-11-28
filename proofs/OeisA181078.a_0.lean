import FormalConjectures.OEIS.«181078»

open PowerSeries OeisA181078

theorem OMA.solution : type_of% @OeisA181078.a_0 := by
  have h (f : ℕ → ℕ → ℤ) : constantCoeff (hannaLog f) = 0 := by simp [hannaLog]
  rw [a, hannaExp, coeff_subst' (.of_constantCoeff_zero' (h _)), finsum_eq_single _ 0] <;> simp [h] <;> omega
