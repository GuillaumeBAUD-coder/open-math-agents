import OMAReductions.R_Transcendental_transcendental_gamma_one_div_six_R1

/-!
# Evaluation of `∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 3)` via Euler's Beta integral

We apply the change of variables `u = x ^ 3` on `(0, 1)` to transform
`∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 3)` into `(1 / 3) * B(1 / 3, 1 / 2)` and then use
`Complex.Gamma_mul_Gamma_eq_betaIntegral`.
-/

namespace OMA.GammaOneDivSixH2

open Real MeasureTheory Set

private lemma image_cube_Ioo : (fun x : ℝ => x ^ 3) '' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
  ext u
  constructor
  · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
    exact ⟨by positivity, by nlinarith [sq_nonneg x]⟩
  · rintro ⟨hu0, hu1⟩
    refine ⟨u ^ ((1 : ℝ) / 3), ⟨Real.rpow_pos_of_pos hu0 _, ?_⟩, ?_⟩
    · exact Real.rpow_lt_one hu0.le hu1 (by norm_num)
    · dsimp only
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
      norm_num

private lemma beta_eval :
    ∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 3) =
      Real.Gamma (1 / 3) * Real.Gamma (1 / 2) / (3 * Real.Gamma (5 / 6)) := by
  have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := ((1 / 3 : ℝ) : ℂ)) (t := ((1 / 2 : ℝ) : ℂ))
    (by simp) (by simp)
  have h56 : ((1 / 3 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) = ((5 / 6 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h56, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at hG
  have hbeta : Complex.betaIntegral ((1 / 3 : ℝ) : ℂ) ((1 / 2 : ℝ) : ℂ) =
      ((3 * ∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 3) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hcongr : ∫ u in Ioo (0 : ℝ) 1,
        (u : ℂ) ^ (((1 / 3 : ℝ) : ℂ) - 1) * (1 - (u : ℂ)) ^ (((1 / 2 : ℝ) : ℂ) - 1) =
        ∫ u in Ioo (0 : ℝ) 1, ((u ^ (-2 / 3 : ℝ) * (1 - u) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      have hu0 : 0 ≤ u := hu.1.le
      have h1u : 0 ≤ 1 - u := by linarith [hu.2]
      have he1 : ((1 / 3 : ℝ) : ℂ) - 1 = ((-2 / 3 : ℝ) : ℂ) := by push_cast; ring
      have he2 : ((1 / 2 : ℝ) : ℂ) - 1 = ((-1 / 2 : ℝ) : ℂ) := by push_cast; ring
      have h1uC : (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
      rw [he1, he2, h1uC, ← Complex.ofReal_cpow hu0, ← Complex.ofReal_cpow h1u, Complex.ofReal_mul]
    have hofR : ∫ u in Ioo (0 : ℝ) 1, ((u ^ (-2 / 3 : ℝ) * (1 - u) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
        ((∫ u in Ioo (0 : ℝ) 1, u ^ (-2 / 3 : ℝ) * (1 - u) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) :=
      integral_ofReal
    rw [hcongr, hofR]
    congr 1
    rw [intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hsub := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Ioo (0 : ℝ) 1) (f := fun x : ℝ => x ^ 3) (f' := fun x : ℝ => 3 * x ^ 2)
      measurableSet_Ioo
      (fun x _ => by
        have hd : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by
          simpa using (hasDerivAt_pow 3 x)
        exact hd.hasDerivWithinAt)
      (fun x hx y hy hxy => by
        have hpos : 0 ≤ x := hx.1.le
        have hpos' : 0 ≤ y := hy.1.le
        exact (pow_left_inj₀ hpos hpos' (by norm_num : 3 ≠ 0)).mp hxy)
      (fun u => u ^ (-2 / 3 : ℝ) * (1 - u) ^ (-1 / 2 : ℝ))
    rw [image_cube_Ioo] at hsub
    rw [hsub, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    have hx0 : 0 < x := hx.1
    have hx3 : x ^ 3 < 1 := by nlinarith [hx.2, sq_nonneg x]
    have h1x : 0 < 1 - x ^ 3 := by linarith
    have habs : |3 * x ^ 2| = 3 * x ^ 2 := abs_of_nonneg (by positivity)
    rw [smul_eq_mul, habs]
    have hpow : (x ^ 3) ^ (-2 / 3 : ℝ) = (x ^ 2)⁻¹ := by
      rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hx0.le]
      norm_num
    have hsqrt : (1 - x ^ 3) ^ (-1 / 2 : ℝ) = 1 / √(1 - x ^ 3) := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg h1x.le,
        ← Real.sqrt_eq_rpow, one_div]
    rw [hpow, hsqrt]
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0.ne'
    field_simp
  rw [hbeta] at hG
  have hG_real : Real.Gamma (1 / 3) * Real.Gamma (1 / 2) =
      Real.Gamma (5 / 6) * (3 * ∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 3)) := by
    exact_mod_cast hG
  have hpos : 0 < Real.Gamma (5 / 6) := Real.Gamma_pos_of_pos (by norm_num)
  rw [eq_div_iff (by positivity)]
  linarith

end OMA.GammaOneDivSixH2

theorem OMA.solution : OMA.R_Transcendental_transcendental_gamma_one_div_six_R1.H2 :=
  OMA.GammaOneDivSixH2.beta_eval
