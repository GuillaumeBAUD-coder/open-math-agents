import FormalConjectures.OEIS.«181082»

open PowerSeries

theorem OMA.solution : type_of% @OeisA181082.a_0 := by
  unfold OeisA181082.a OeisA181082.hannaExp
  generalize hg : OeisA181082.hannaLog
    (fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k) else 0) = g
  have hzero : constantCoeff g = 0 := by
    subst g
    simp [OeisA181082.hannaLog]
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_eq,
    constantCoeff_subst (HasSubst.of_constantCoeff_zero' hzero), finsum_eq_single _ 0]
  · simp
  · intro n hn
    change coeff n (exp ℚ) • constantCoeff (g ^ n) = 0
    rw [map_pow, hzero, zero_pow hn, smul_zero]
