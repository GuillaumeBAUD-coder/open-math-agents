import FormalConjectures.OEIS.«181078»

/-! The quadratic coefficient of the exponential has support only at powers one and two. -/

open PowerSeries OeisA181078 in
theorem OMA.solution : type_of% @OeisA181078.a_2 := by
  let g := hannaLog fun n k => ((n + k - 1).choose k : ℤ) ^ (n + k - 1)
  change coeff 2 (subst g (exp ℚ)) = 2
  have h0 : g.constantCoeff = 0 := by simp [g, hannaLog]
  have h1 : coeff 1 g = 1 := by simp [g, hannaLog, coeff_mk]
  have h2 : coeff 2 g = 3 / 2 := by
    norm_num [g, hannaLog, coeff_mk, Finset.sum_Icc_succ_top]
  have hsq : coeff 2 (g ^ 2) = 1 := by
    simp [pow_two, coeff_mul, Finset.Nat.antidiagonal_succ_succ',
      coeff_zero_eq_constantCoeff_apply, h0, h1]
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' h0),
    finsum_eq_sum_of_support_subset (s := ({1, 2} : Finset ℕ))]
  · norm_num [coeff_exp, h2, hsq, Nat.factorial]
  · rintro (_ | _ | _ | n) hn
    · simp at hn
    · simp
    · simp
    · have hz := X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr h0) (n + 3)) 2 (by omega)
      simp [hz] at hn
