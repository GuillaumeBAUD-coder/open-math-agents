import OMAReductions.R_wpc_local_smoothing_conjecture_R1

-- Step wpc-local-smoothing-conjecture.R1.H2: hypothesis H2 of reduction wpc-local-smoothing-conjecture.R1
-- Credit: @luciusacarr

/-!
Both functions are parametric Bochner integrals `x ↦ ∫ ξ, F (x, ξ)` with `F` jointly measurable,
so they are strongly measurable by `StronglyMeasurable.integral_prod_right'`. The inner Fourier
transform is measurable for the same reason.
-/

open MeasureTheory OMA.S_wpc_local_smoothing_conjecture

namespace OMA.WpcLocalSmoothingH2

lemma fourier_meas {n : ℕ} {f : Space n → ℂ} (hf : Measurable f) :
    Measurable (angularFourier f) := by
  have h : StronglyMeasurable (fun p : Space n × Space n =>
      Complex.exp (-Complex.I * ((inner ℝ p.2 p.1 : ℝ) : ℂ)) * f p.2) := by
    apply Measurable.stronglyMeasurable
    exact (Continuous.measurable (by fun_prop)).mul (hf.comp measurable_snd)
  exact h.integral_prod_right'.measurable

end OMA.WpcLocalSmoothingH2

open OMA.WpcLocalSmoothingH2 in
theorem OMA.solution : OMA.R_wpc_local_smoothing_conjecture_R1.H2 := by
  intro n α f
  have hF : Measurable (angularFourier (f : Space n → ℂ)) := fourier_meas f.continuous.measurable
  constructor
  · have h : StronglyMeasurable (fun p : Space n × Space n =>
        Complex.exp (Complex.I * ((inner ℝ p.1 p.2 : ℝ) : ℂ)) *
          (((1 + ‖p.2‖ ^ 2) ^ (α / 2) : ℝ) • angularFourier (f : Space n → ℂ) p.2)) := by
      apply Measurable.stronglyMeasurable
      refine (Continuous.measurable (by fun_prop)).mul ?_
      have hr : Measurable (fun p : Space n × Space n => ((1 + ‖p.2‖ ^ 2) ^ (α / 2) : ℝ)) := by
        fun_prop
      exact hr.smul (hF.comp measurable_snd)
    have hm := h.integral_prod_right' (ν := volume)
    unfold besselPotential angularInverse
    exact (hm.measurable.const_smul (((2 * Real.pi) ^ n)⁻¹ : ℝ) :)
  · have h : StronglyMeasurable (fun p : (Space n × ℝ) × Space n =>
        Complex.exp (Complex.I * ((inner ℝ p.1.1 p.2 : ℝ) : ℂ)) *
          (Complex.exp (-Complex.I * ((-p.1.2 * ‖p.2‖ : ℝ) : ℂ)) *
            angularFourier (f : Space n → ℂ) p.2)) := by
      apply Measurable.stronglyMeasurable
      refine (Continuous.measurable (by fun_prop)).mul ?_
      exact (Continuous.measurable (by fun_prop)).mul (hF.comp measurable_snd)
    have hm := h.integral_prod_right' (ν := volume)
    unfold halfWaveIntegral angularInverse
    exact (hm.measurable.const_smul (((2 * Real.pi) ^ n)⁻¹ : ℝ) :)
