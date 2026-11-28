import FormalConjectures.OEIS.«181082»

/-! The linear term of the exponential is the only contribution. The general
coefficient-of-a-power formula handles all other indices uniformly. -/

open OeisA181082 PowerSeries in
theorem OMA.solution : type_of% @OeisA181082.a_1 := by
  let L := hannaLog fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k) else 0
  have h0 : L.constantCoeff = 0 := by simp [L, hannaLog]
  change coeff 1 (subst L (exp ℚ)) = 1
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' h0), finsum_eq_single _ 1]
  · simp [L, hannaLog]
  · rintro (_ | _ | n) hn <;> simp_all [coeff_one_pow]
