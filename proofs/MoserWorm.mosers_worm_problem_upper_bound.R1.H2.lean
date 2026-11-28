import OMAReductions.R_MoserWorm_mosers_worm_problem_upper_bound_R1

open MeasureTheory Set
open scoped ENNReal

namespace OMA.H2proof

noncomputable def a : ℝ := 129 / 500
noncomputable def b : ℝ := 501 / 500

lemma integral_tri : ∫ x in (-a)..a, b * (1 - |x| / a) = 64629 / 250000 := by
  have ha : (0:ℝ) < a := by unfold a; norm_num
  have h1 : ∫ x in (-a)..0, b * (1 - |x| / a) = ∫ x in (-a)..0, b * (1 + x / a) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    simp only [abs_of_nonpos hx.2]; ring
  have h2 : ∫ x in (0:ℝ)..a, b * (1 - |x| / a) = ∫ x in (0:ℝ)..a, b * (1 - x / a) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ha.le] at hx
    simp only [abs_of_nonneg hx.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), h1, h2]
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub,
    intervalIntegral.integral_add, intervalIntegral.integral_div, integral_id, integral_const,
    intervalIntegrable_const, intervalIntegral.intervalIntegrable_id,
    IntervalIntegrable.div_const]
  simp
  unfold a b
  norm_num

end OMA.H2proof

open OMA.H2proof in
theorem OMA.solution : OMA.R_MoserWorm_mosers_worm_problem_upper_bound_R1.H2 := by

  unfold OMA.R_MoserWorm_mosers_worm_problem_upper_bound_R1.H2
  have ha : (0:ℝ) < a := by unfold a; norm_num
  have hb : (0:ℝ) < b := by unfold b; norm_num
  let T : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ |p.1| / a + p.2 / b ≤ 1}
  have hTm : MeasurableSet T := by
    apply MeasurableSet.inter
    · exact measurableSet_le measurable_const measurable_snd
    · exact measurableSet_le (((continuous_fst.abs).measurable.div_const _).add (measurable_snd.div_const _)) measurable_const
  have hpres : MeasurePreserving
      ((MeasurableEquiv.finTwoArrow).toFun ∘ (@WithLp.ofLp 2 (Fin 2 → ℝ)))
      (volume : Measure (EuclideanSpace ℝ (Fin 2))) (volume : Measure (ℝ × ℝ)) :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  have hpre : (volume : Measure (EuclideanSpace ℝ (Fin 2))) {x : EuclideanSpace ℝ (Fin 2) | 0 ≤ x 1 ∧ |x 0| / (129 / 500 : ℝ) + x 1 / (501 / 500 : ℝ) ≤ 1}
      = volume T := by
    rw [← hpres.measure_preimage hTm.nullMeasurableSet]
    rfl
  rw [hpre, Measure.volume_eq_prod, Measure.prod_apply hTm]
  have hsec : ∀ x : ℝ, volume (Prod.mk x ⁻¹' T) = ENNReal.ofReal (b * (1 - |x| / a)) := by
    intro x
    have : Prod.mk x ⁻¹' T = Icc 0 (b * (1 - |x| / a)) := by
      ext y
      simp only [T, mem_preimage, mem_setOf_eq, mem_Icc]
      constructor
      · rintro ⟨h0, h1⟩
        refine ⟨h0, ?_⟩
        have : y / b ≤ 1 - |x| / a := by linarith
        rw [div_le_iff₀ hb] at this; linarith
      · rintro ⟨h0, h1⟩
        refine ⟨h0, ?_⟩
        have : y ≤ (1 - |x| / a) * b := by linarith
        have : y / b ≤ 1 - |x| / a := by rwa [div_le_iff₀ hb]
        linarith
    rw [this, Real.volume_Icc]; simp
  simp_rw [hsec]
  have hsupp : Function.support (fun x : ℝ => ENNReal.ofReal (b * (1 - |x| / a))) ⊆ Icc (-a) a := by
    intro x hx
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hx
    have h : 0 < 1 - |x| / a := by
      by_contra h; push_neg at h; nlinarith
    have : |x| / a < 1 := by linarith
    rw [div_lt_one ha] at this
    exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  rw [← setLIntegral_eq_of_support_subset hsupp]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith), integral_tri]
  · exact (Continuous.integrableOn_Icc (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have : |x| ≤ a := abs_le.mpr hx
    have : |x| / a ≤ 1 := (div_le_one ha).mpr this
    exact mul_nonneg hb.le (by linarith)
