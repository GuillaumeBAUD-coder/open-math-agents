import FormalConjectures.Wikipedia.PompeiuProblem
import Mathlib.Analysis.Fourier.Inversion

/-! A Fourier transform argument using centered second differences of the ball indicator. -/

open Filter MeasureTheory Complex Module Metric Real
open scoped Topology FourierTransform RealInnerProductSpace ComplexConjugate

namespace OMA.Pompeiu

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

-- Use the Gaussian regularization from Mathlib.Analysis.Fourier.Inversion at the origin.
private theorem nonneg_at_zero {f : V → ℂ} (hf : Integrable f)
    (hc : ContinuousAt f 0) (hp : ∀ w, 0 ≤ (𝓕 f w).re) : 0 ≤ (f 0).re := by
  have lim := Real.tendsto_integral_gaussian_smul' hf hc
  apply ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp lim)
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc'
  let g : V → ℂ := fun w ↦ Complex.exp (-(c : ℂ)⁻¹ * ‖w‖ ^ 2)
  have hg : Integrable g := by
    simpa [g] using (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := V) (b := (c : ℂ)⁻¹) (by simpa) 0 (0 : V))
  have eqg (w : V) : 𝓕 g w = (π * c : ℂ) ^ (finrank ℝ V / 2 : ℂ) *
      Complex.exp (-π ^ 2 * c * ‖(0 : V) - w‖ ^ 2) := by
    rw [show 𝓕 g w = _ from fourier_gaussian_innerProductSpace
      (V := V) (b := (c : ℂ)⁻¹) (by simpa) w]
    simp [div_eq_mul_inv]
    ring_nf
    simp
  change 0 ≤ (∫ w : V, _ • f w).re
  simp_rw [← eqg]
  have swap : (∫ w, 𝓕 g w • f w) = ∫ w, g w • 𝓕 f w := by
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner hg hf)
  rw [swap]
  by_cases hi : Integrable (fun w ↦ g w • 𝓕 f w)
  · rw [← RCLike.re_eq_complex_re, ← integral_re hi]
    apply integral_nonneg
    intro w
    have he : g w = (Real.exp (-c⁻¹ * ‖w‖ ^ 2) : ℝ) := by simp [g]
    change 0 ≤ (g w * 𝓕 f w).re
    rw [he, re_ofReal_mul]
    exact mul_nonneg (Real.exp_pos (-c⁻¹ * ‖w‖ ^ 2)).le (hp w)
  · rw [integral_undef hi]
    simp

private def secondDiff (a : V) (f : V → ℂ) : V → ℂ :=
  (f ∘ fun x ↦ x + a) + (f ∘ fun x ↦ x + -a) + (-2 : ℂ) • f

private theorem secondDiff_integrable (a : V) {f : V → ℂ} (hf : Integrable f) : Integrable (secondDiff a f) :=
  ((hf.comp_add_right a).add
    (hf.comp_add_right (-a))).add (hf.smul _)

private theorem fourier_secondDiff (a : V) {f : V → ℂ} (hf : Integrable f) (w : V) :
    𝓕 (secondDiff a f) w = ((2 * ((Real.fourierChar ⟪a, w⟫ : Circle) : ℂ).re - 2 : ℝ) : ℂ) * 𝓕 f w := by
  have add {u v : V → ℂ} (hu : Integrable u) (hv : Integrable v) :
      𝓕 (u + v) w = 𝓕 u w + 𝓕 v w :=
    congrFun (VectorFourier.fourierIntegral_add (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner hu hv) w
  have tr (b : V) : 𝓕 (f ∘ fun x ↦ x + b) w =
      Real.fourierChar ⟪b, w⟫ • 𝓕 f w :=
    congrFun (VectorFourier.fourierIntegral_comp_add_right _ volume (innerₗ V) f b) w
  have sc : 𝓕 ((-2 : ℂ) • f) w = (-2 : ℂ) • 𝓕 f w :=
    congrFun (VectorFourier.fourierIntegral_const_smul _ volume (innerₗ V) f (-2)) w
  have hi (b : V) : Integrable (f ∘ fun x ↦ x + b) := hf.comp_add_right b
  rw [secondDiff, add ((hi a).add (hi (-a))) (hf.smul (-2 : ℂ)), add (hi a) (hi (-a)), tr, tr, sc]
  simp only [inner_neg_left, AddChar.map_neg_eq_inv, Circle.smul_def, Circle.coe_inv_eq_conj,
    smul_eq_mul, ofReal_sub, ofReal_mul, ofReal_ofNat]
  rw [← add_mul, Complex.add_conj, ofReal_mul, ofReal_ofNat]
  ring

omit [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
private theorem secondDiff_continuousAt (a x : V) {f : V → ℂ} (h₁ : ContinuousAt f (x + a))
    (h₂ : ContinuousAt f (x + -a)) (h₃ : ContinuousAt f x) : ContinuousAt (secondDiff a f) x := by
  unfold secondDiff
  apply ContinuousAt.add
  · apply ContinuousAt.add
    · exact h₁.comp (f := fun y ↦ y + a) (continuous_id.add_const a).continuousAt
    · exact h₂.comp (f := fun y ↦ y + -a) (continuous_id.add_const (-a)).continuousAt
  · exact h₃.const_smul (-2 : ℂ)

private noncomputable def ballIndicator (c : V) (r : ℝ) : V → ℂ :=
  (ball c r).indicator (fun _ ↦ 1)

private theorem ballIndicator_integrable (c : V) (r : ℝ) : Integrable (ballIndicator c r) :=
  (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)

omit [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
private theorem ballIndicator_continuousAt (r : ℝ) (x : V) (hx : ‖x‖ ≠ r) : ContinuousAt (ballIndicator 0 r) x := by
  apply continuousOn_const.continuousAt_indicator
  exact fun h ↦ hx (by simpa [Metric.mem_sphere] using frontier_ball_subset_sphere h)

private theorem exists_negative_frequency [Nontrivial V] {r : ℝ} (hr : 0 < r) :
    ∃ w : V, (𝓕 (ballIndicator (0 : V) r) w).re < 0 := by
  by_contra! hp
  obtain ⟨a, ha⟩ := exists_norm_eq V (show 0 ≤ 3 * r / 4 by linarith)
  have hdouble : ‖a + a‖ = 2 * ‖a‖ := by
    rw [← two_smul ℝ a, norm_smul]
    norm_num
  have hneg : ‖-a + -a‖ = ‖a + a‖ := by rw [show -a + -a = -(a + a) by abel, norm_neg]
  -- The five sample points lie strictly inside or strictly outside the ball.
  have cont : ContinuousAt (secondDiff a (secondDiff a (ballIndicator (0 : V) r))) 0 := by
    apply secondDiff_continuousAt <;> apply secondDiff_continuousAt <;> apply ballIndicator_continuousAt <;>
      simp [hneg, hdouble, ha] <;> linarith
  have h := nonneg_at_zero (secondDiff_integrable a (secondDiff_integrable a (ballIndicator_integrable (0 : V) r))) cont (by
    intro w
    rw [fourier_secondDiff _ (secondDiff_integrable _ (ballIndicator_integrable _ _)), fourier_secondDiff _ (ballIndicator_integrable _ _)]
    simp only [re_ofReal_mul]
    rw [← mul_assoc]
    exact mul_nonneg (mul_self_nonneg _) (hp w))
  -- The twice-differenced indicator takes the value -2 at the origin.
  have ha₁ : ‖a‖ < r := by linarith
  have ha₂ : ¬ ‖a + a‖ < r := by rw [hdouble]; linarith
  simp [secondDiff, ballIndicator, Metric.mem_ball, dist_zero_right, hneg, ha₁, ha₂, hr] at h
  norm_num at h

private theorem fourier_ballIndicator (c : V) (r : ℝ) (w : V) :
    𝓕 (ballIndicator c r) w = ∫ x in ball c r, (Real.fourierChar (-⟪x, w⟫) : ℂ) := by
  rw [Real.fourier_eq, ← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ ball c r <;> simp [ballIndicator, hx, Circle.smul_def]

private theorem fourier_ballIndicator_conj (r : ℝ) (w : V) :
    conj (𝓕 (ballIndicator (0 : V) r) w) = 𝓕 (ballIndicator (0 : V) r) w := by
  rw [Real.fourier_eq, ← integral_conj, ← integral_neg_eq_self
    (fun x : V ↦ Real.fourierChar (-⟪x, w⟫) • ballIndicator 0 r x) volume]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : ‖x‖ < r <;>
    simp [ballIndicator, Metric.mem_ball, hx, inner_neg_left, Circle.smul_def,
      AddChar.map_neg_eq_inv]

private theorem exists_zero_frequency [Nontrivial V] {r : ℝ} (hr : 0 < r) :
    ∃ w : V, 𝓕 (ballIndicator (0 : V) r) w = 0 := by
  obtain ⟨v, hv⟩ := exists_negative_frequency (V := V) hr
  have hc : Continuous (𝓕 (ballIndicator (0 : V) r)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (ballIndicator_integrable _ _)
  have h₀ : 0 ≤ (𝓕 (ballIndicator (0 : V) r) 0).re := by
    rw [fourier_ballIndicator]
    simp
  obtain ⟨w, hw⟩ := intermediate_value_univ v 0 (Complex.continuous_re.comp hc)
    (show 0 ∈ Set.Icc _ _ from ⟨hv.le, h₀⟩)
  refine ⟨w, Complex.ext hw ?_⟩
  have := congrArg Complex.im (fourier_ballIndicator_conj r w)
  simp only [Complex.conj_im, Complex.zero_im] at *
  linarith

end OMA.Pompeiu

open OMA.Pompeiu PompeiuProblem

-- Credit: @MrSeizy
theorem OMA.solution : type_of% @PompeiuProblem.ball_not_hasPompeiuProperty := by
  intro N Ω hball hp
  obtain ⟨c, r, hr, rfl⟩ := hball
  let V := EuclideanSpace ℝ (Fin (N + 1))
  obtain ⟨w, hw⟩ := exists_zero_frequency (V := V) hr
  let e : V → ℂ := fun x ↦ (Real.fourierChar (-⟪x, w⟫) : ℂ)
  have ec : Continuous e := by
    exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_id.inner continuous_const).neg)
  have translated (b : V) : 𝓕 (ballIndicator b r) w = 0 := by
    have h : ballIndicator b r = (ballIndicator 0 r) ∘ fun x ↦ x + -b := by
      funext x
      simp only [ballIndicator, Function.comp_apply, Set.indicator, Metric.mem_ball,
        dist_eq_norm, sub_eq_add_neg, neg_zero, add_zero]
    rw [h]
    change VectorFourier.fourierIntegral _ _ _ _ _ = 0
    rw [VectorFourier.fourierIntegral_comp_add_right]
    change _ • 𝓕 (ballIndicator (0 : V) r) w = 0
    rw [hw, smul_zero]
  have van (σ : RigidMotion N) : (∫ x in σ '' ball c r, (e x).re) = 0 := by
    rw [show σ '' ball c r = ball (σ c) r from σ.toIsometryEquiv.image_ball c r]
    have hi : IntegrableOn e (ball (σ c) r) :=
      (ec.continuousOn.integrableOn_compact (isCompact_closedBall (σ c) r)).mono_set
        ball_subset_closedBall
    change (∫ x in ball (σ c) r, RCLike.re (e x)) = 0
    rw [integral_re hi]
    have hz : (∫ x in ball (σ c) r, e x) = 0 := (fourier_ballIndicator _ _ _).symm.trans (translated _)
    exact congrArg (fun z : ℂ ↦ RCLike.re z) hz
  have h := hp (fun x ↦ (e x).re) (Complex.continuous_re.comp ec) van 0
  simp [e] at h
