import OMAReductions.R_wpc_local_smoothing_conjecture_R1

/-!
# Proof of wpc-local-smoothing-conjecture.R1.H2

Proves measurability of `besselPotential α f` on `Space n` and of
`(x, t) ↦ halfWaveIntegral (-t) f x` on `Space n × ℝ` for every Schwartz function `f`.

Because Lebesgue measure `volume` on `Space n = EuclideanSpace ℝ (Fin n)` is `SFinite`,
Mathlib's `StronglyMeasurable.integral_prod_right` yields strong measurability of the
parameter-dependent Bochner integrals `angularFourier f`, `besselPotential α f`, and
`fun z : Space n × ℝ ↦ halfWaveIntegral (-z.2) f z.1` directly from continuity of the
phase factors, the Bessel weight, and `f`.
-/

-- Proof of step wpc-local-smoothing-conjecture.R1.H2
-- Credit: @mvanhorn

open MeasureTheory OMA.S_wpc_local_smoothing_conjecture
open scoped RealInnerProductSpace

section LocalSmoothingMeasurability

private lemma stronglyMeasurable_angularFourier {n : ℕ} (f : SchwartzMap (Space n) ℂ) :
    StronglyMeasurable (angularFourier f) := by
  have hcont : Continuous (fun p : Space n × Space n ↦
      Complex.exp (-Complex.I * ((inner ℝ p.2 p.1 : ℝ) : ℂ)) * f p.2) := by
    refine Continuous.mul ?_ (f.continuous.comp continuous_snd)
    refine Complex.continuous_exp.comp (continuous_const.mul ?_)
    exact Complex.continuous_ofReal.comp (continuous_inner.comp (continuous_snd.prodMk continuous_fst))
  exact hcont.stronglyMeasurable.integral_prod_right

theorem OMA.solution : OMA.R_wpc_local_smoothing_conjecture_R1.H2 := by
  intro n α f
  have hF : StronglyMeasurable (angularFourier f) := stronglyMeasurable_angularFourier f
  constructor
  · have hweight : Continuous (fun ξ : Space n ↦ ((1 + ‖ξ‖ ^ 2) ^ (α / 2) : ℝ)) := by
      refine Continuous.rpow_const ?_ (fun ξ => Or.inl ?_)
      · exact continuous_const.add (continuous_norm.pow 2)
      · positivity
    have hg : StronglyMeasurable (fun ξ : Space n ↦
        ((1 + ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) • angularFourier f ξ) :=
      hweight.stronglyMeasurable.smul hF
    have hphase : Continuous (fun p : Space n × Space n ↦
        Complex.exp (Complex.I * ((inner ℝ p.1 p.2 : ℝ) : ℂ))) :=
      Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp continuous_inner))
    have hint : StronglyMeasurable (fun x : Space n ↦
        ∫ ξ, Complex.exp (Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) *
          (((1 + ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) • angularFourier f ξ)) :=
      (hphase.stronglyMeasurable.mul (hg.comp_measurable measurable_snd)).integral_prod_right
    change Measurable (fun x : Space n ↦ (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
      ∫ ξ, Complex.exp (Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) *
        (((1 + ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) • angularFourier f ξ))
    exact (hint.const_smul (((2 * Real.pi) ^ n)⁻¹ : ℝ)).measurable
  · have hphase1 : Continuous (fun p : (Space n × ℝ) × Space n ↦
        Complex.exp (Complex.I * ((inner ℝ p.1.1 p.2 : ℝ) : ℂ))) :=
      Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_inner.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))))
    have hphase2 : Continuous (fun p : (Space n × ℝ) × Space n ↦
        Complex.exp (-Complex.I * (((-p.1.2) * ‖p.2‖ : ℝ) : ℂ))) :=
      Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp
          (((continuous_snd.comp continuous_fst).neg).mul (continuous_norm.comp continuous_snd))))
    have hint : StronglyMeasurable (fun z : Space n × ℝ ↦
        ∫ ξ, Complex.exp (Complex.I * ((inner ℝ z.1 ξ : ℝ) : ℂ)) *
          (Complex.exp (-Complex.I * ((-z.2) * ‖ξ‖ : ℝ)) * angularFourier f ξ)) :=
      (hphase1.stronglyMeasurable.mul
        (hphase2.stronglyMeasurable.mul (hF.comp_measurable measurable_snd))).integral_prod_right
    change Measurable (fun z : Space n × ℝ ↦ (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
      ∫ ξ, Complex.exp (Complex.I * ((inner ℝ z.1 ξ : ℝ) : ℂ)) *
        (Complex.exp (-Complex.I * ((-z.2) * ‖ξ‖ : ℝ)) * angularFourier f ξ))
    exact (hint.const_smul (((2 * Real.pi) ^ n)⁻¹ : ℝ)).measurable

end LocalSmoothingMeasurability
