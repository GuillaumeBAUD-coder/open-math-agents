import OMAReductions.R_Erdos297_erdos_297_variants_general_R1
/-! The primitive of a bounded rescaled kernel parametrizes the reciprocal mass. -/
open Set MeasureTheory Real Erdos297
namespace Calibration297
noncomputable def K (u : ℝ) : ℝ := if 0 < u then 1 / (u * (1 + exp (1/u))) else 0
noncomputable def F (b : ℝ) := ∫ u in (0:ℝ)..b, K u

lemma k_nonneg (u : ℝ) : 0 ≤ K u := by
  unfold K
  split_ifs <;> positivity

lemma k_le (u : ℝ) : K u ≤ 1 := by
  by_cases hu : 0 < u
  · rw [K, if_pos hu, div_le_iff₀ (by positivity : 0 < u * (1 + exp (1/u))), one_mul]
    have h := Real.add_one_le_exp (1/u)
    have h' : 1/u ≤ 1 + exp (1/u) := by linarith
    simpa [hu.ne', mul_comm] using (div_le_iff₀ hu).1 h'
  · simp [K, hu]

lemma k_int (a b : ℝ) : IntervalIntegrable K volume a b := by
  apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun'
  · apply Measurable.aestronglyMeasurable
    unfold K
    exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const
  · exact Filter.Eventually.of_forall fun u => by simpa [Real.norm_eq_abs, abs_of_nonneg (k_nonneg u)] using k_le u

lemma f_strict : StrictMonoOn F (Ioi 0) := by
  intro a ha b hb hab
  have hcont : ContinuousOn K (Icc a b) := by
    apply ContinuousOn.congr (f := fun u : ℝ => 1 / (u * (1 + exp (1/u))))
    · apply continuousOn_const.div
      · apply continuousOn_id.mul
        apply continuousOn_const.add
        apply Real.continuous_exp.comp_continuousOn
        exact continuousOn_const.div continuousOn_id fun u hu => (lt_of_lt_of_le ha hu.1).ne'
      · intro u hu
        have : 0 < u := lt_of_lt_of_le ha hu.1
        positivity
    · intro u hu
      simp [K, lt_of_lt_of_le ha hu.1]
  have hp := intervalIntegral.integral_pos hab hcont (fun u _ => k_nonneg u)
      ⟨a, ⟨le_rfl, hab.le⟩, by have : 0 < a := ha; simp [K, this]; positivity⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals (k_int 0 a) (k_int a b)
  unfold F
  linarith

lemma mass_scale {l : ℝ} (hl : 0 < l) : massIntegral l = F (1/l) := by
  unfold massIntegral F
  have h := intervalIntegral.inv_smul_integral_comp_div (a := (0:ℝ)) (b := 1) K l
  rw [zero_div, smul_eq_mul, ← intervalIntegral.integral_const_mul] at h
  refine Eq.trans (intervalIntegral.integral_congr ?_) h
  intro u hu
  rw [uIcc_of_le zero_le_one] at hu
  rcases hu.1.eq_or_lt with rfl | hp
  · simp [K]
  · change 1 / (u * (1 + exp (l/u))) = l⁻¹ * K (u/l)
    rw [K, if_pos (div_pos hp hl)]
    have harg : 1 / (u/l) = l/u := by field_simp
    rw [harg]
    field_simp

lemma mass_zero {l : ℝ} (hl : l ≤ 0) : massIntegral l = 0 := by
  by_contra h
  have hi : IntervalIntegrable (fun y : ℝ => 1 / (y * (1 + exp (l/y)))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_of_integral_ne_zero h
  have h' : IntervalIntegrable (fun y : ℝ => y⁻¹) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
    apply (hi.1.const_mul 2).mono_nonneg (by fun_prop)
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with y hy
      exact (inv_pos.2 hy.1).le
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with y hy
      have hy' : 0 < y := hy.1
      have he : exp (l/y) ≤ 1 := Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg hl hy'.le)
      change y⁻¹ ≤ 2 * (1 / (y * (1 + exp (l/y))))
      rw [← mul_div_assoc, mul_one, le_div_iff₀ (by positivity)]
      calc
        y⁻¹ * (y * (1 + exp (l/y))) = 1 + exp (l/y) := by field_simp
        _ ≤ 2 := by linarith
  simp [intervalIntegrable_inv_iff] at h'

lemma exists_upper (x : ℝ) (hx : 0 < x) : ∃ b : ℝ, 0 ≤ b ∧ x ≤ F b := by
  let C := 1 + exp 1
  let b := exp (C*x)
  have hc : 0 < C := by dsimp [C]; positivity
  have hb : 1 ≤ b := Real.one_le_exp (by positivity)
  have hi : IntervalIntegrable (fun u : ℝ => u⁻¹) volume 1 b := by
    rw [intervalIntegrable_inv_iff, uIcc_of_le hb]
    simp
  have hlow := intervalIntegral.integral_mono_on hb (hi.const_mul C⁻¹) (k_int 1 b) (by
    intro u hu
    have hu' : 0 < u := lt_of_lt_of_le zero_lt_one hu.1
    have he : exp (1/u) ≤ exp 1 := Real.exp_le_exp.2 ((div_le_one hu').2 hu.1)
    change C⁻¹ * u⁻¹ ≤ K u
    rw [K, if_pos hu', one_div, ← mul_inv_rev]
    apply inv_anti₀ (by positivity)
    exact mul_le_mul_of_nonneg_left (by dsimp [C]; linarith) hu'.le)
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hb), div_one, Real.log_exp] at hlow
  have hadd := intervalIntegral.integral_add_adjacent_intervals (k_int 0 1) (k_int 1 b)
  have hn : 0 ≤ ∫ u in (0:ℝ)..1, K u := intervalIntegral.integral_nonneg zero_le_one (fun u _ => k_nonneg u)
  refine ⟨b, zero_le_one.trans hb, ?_⟩
  rw [show C⁻¹ * (C*x) = x by field_simp] at hlow
  unfold F
  linarith

theorem calibrated (x : ℝ) (hx : 0 < x) : ∃! l : ℝ, massIntegral l = x := by
  obtain ⟨b, hb, hub⟩ := exists_upper x hx
  have hcont : Continuous F := intervalIntegral.continuous_primitive k_int 0
  have hz : F 0 = 0 := by simp [F]
  obtain ⟨u, hu, heu⟩ := intermediate_value_Icc hb hcont.continuousOn (show x ∈ Icc (F 0) (F b) from ⟨by simpa only [hz] using hx.le, hub⟩)
  have hu' : 0 < u := lt_of_le_of_ne hu.1 (fun h => by rw [← h, hz] at heu; linarith)
  refine ⟨1/u, ?_, ?_⟩
  · change massIntegral (1/u) = x
    rw [mass_scale (one_div_pos.2 hu')]
    simpa using heu
  · intro z hz'
    have hp : 0 < z := by
      by_contra! h
      rw [mass_zero h] at hz'
      linarith
    have heq : 1/z = u := f_strict.injOn (one_div_pos.2 hp) hu' ((mass_scale hp).symm.trans (hz'.trans heu.symm))
    rw [← heq]
    simp
end Calibration297

theorem OMA.solution : OMA.R_Erdos297_erdos_297_variants_general_R1.H1 := by
  intro x hx
  exact Calibration297.calibrated x (by exact_mod_cast hx)
