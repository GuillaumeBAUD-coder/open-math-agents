import OMAStatements.S_mo_326993

open MeasureTheory Set Metric
open scoped ENNReal

namespace CoulombEnergy

abbrev E := EuclideanSpace ℝ (Fin 3)

noncomputable def density (a x : E) : ℝ := ‖x - a‖ ^ (-(8 / 3) : ℝ)

theorem densityNonneg (a x : E) : 0 ≤ density a x :=
  Real.rpow_nonneg (norm_nonneg _) _

theorem densityIntegrable (a : E) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (density a) (ball a R) := by
  have hRadial : IntegrableOn (fun x : E => ‖x‖ ^ (-(8 / 3) : ℝ)) (ball 0 R) := by
    refine (integrableOn_fun_norm_addHaar (volume : Measure E)
      (f := fun y : ℝ => y ^ (-(8 / 3) : ℝ))).2 ?_
    have hOneDim : IntegrableOn (fun y : ℝ => y ^ (-(2 / 3) : ℝ)) (Ioo 0 R) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hR).2 (by norm_num)
    apply hOneDim.congr_fun _ measurableSet_Ioo
    intro y hy
    have hy0 := hy.1
    simp only [finrank_euclideanSpace_fin, Nat.reduceSub, smul_eq_mul]
    rw [← Real.rpow_natCast, ← Real.rpow_add hy0]
    congr 1
    norm_num
  have hPreimage : (fun x : E => x - a) ⁻¹' ball 0 R = ball a R := by
    ext x
    simp [Metric.mem_ball, dist_eq_norm]
  have hEmbedding : MeasurableEmbedding (fun x : E => x - a) := by
    simpa [sub_eq_add_neg] using (MeasurableEquiv.addRight (-a)).measurableEmbedding
  have translated := (MeasurePreserving.integrableOn_comp_preimage
    (measurePreserving_sub_right (volume : Measure E) a) hEmbedding).2 hRadial
  rw [hPreimage] at translated
  exact translated

theorem densityLower (a x : E) {t : ℝ} (ht : 0 < t) (hx : x ∈ ball a (t ^ 3))
    (hxa : x ≠ a) : (t ^ 8)⁻¹ ≤ density a x := by
  have hnorm : 0 < ‖x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxa)
  have hle : ‖x - a‖ ≤ t ^ 3 := by
    simpa only [dist_eq_norm] using (mem_ball.mp hx).le
  have h := Real.rpow_le_rpow_of_nonpos hnorm hle (by norm_num : (-(8 / 3) : ℝ) ≤ 0)
  have hpower : (t ^ 3) ^ (-(8 / 3) : ℝ) = (t ^ 8)⁻¹ := by
    rw [← Real.rpow_natCast_mul ht.le 3, show (3 : ℕ) * (-(8 / 3) : ℝ) =
      -(8 : ℝ) by norm_num, Real.rpow_neg ht.le]
    norm_cast
  rw [hpower] at h
  exact h

theorem kernelLower (a x y : E) {t : ℝ} (ht : 0 < t) (hx : x ∈ ball a (t ^ 3))
    (hy : y ∈ ball a (t ^ 3)) (hxa : x ≠ a) (hya : y ≠ a) (hyx : y ≠ x) :
    1 / (2 * t ^ 19) ≤ density a x * density a y / ‖x - y‖ := by
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx.symm)
  have hbound : ‖x - y‖ ≤ 2 * t ^ 3 := by
    rw [← dist_eq_norm]
    have h := dist_triangle x a y
    rw [dist_comm a y] at h
    linarith [mem_ball.mp hx, mem_ball.mp hy]
  calc
    1 / (2 * t ^ 19) = ((t ^ 8)⁻¹ * (t ^ 8)⁻¹) / (2 * t ^ 3) := by
      field_simp
    _ ≤ ((t ^ 8)⁻¹ * (t ^ 8)⁻¹) / ‖x - y‖ :=
      div_le_div_of_nonneg_left (by positivity) hpos hbound
    _ ≤ density a x * density a y / ‖x - y‖ :=
      div_le_div_of_nonneg_right
        (mul_le_mul (densityLower a x ht hx hxa) (densityLower a y ht hy hya)
          (by positivity) (densityNonneg a x)) hpos.le

noncomputable def energy (a : E) (U : Set E) : ℝ≥0∞ :=
  ∫⁻ x in U, ∫⁻ y in U, ENNReal.ofReal (density a x * density a y / ‖x - y‖)

theorem energyBall (a : E) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal ((Real.pi * 4 / 3) ^ 2 / (2 * t)) ≤ energy a (ball a (t ^ 3)) := by
  let B := ball a (t ^ 3)
  have hB : MeasurableSet B := measurableSet_ball
  have hVolume : (volume : Measure E) B = ENNReal.ofReal ((t ^ 3) ^ 3 * (Real.pi * 4 / 3)) := by
    simp only [B, EuclideanSpace.volume_ball_fin_three]
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  calc
    ENNReal.ofReal ((Real.pi * 4 / 3) ^ 2 / (2 * t)) =
        (∫⁻ _x in B, ∫⁻ _y in B, ENNReal.ofReal (1 / (2 * t ^ 19))) := by
      rw [lintegral_const, lintegral_const, Measure.restrict_apply_univ, hVolume]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    _ ≤ energy a B := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB, (volume.restrict B).ae_ne a] with x hx hxa
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB, (volume.restrict B).ae_ne a,
        (volume.restrict B).ae_ne x] with y hy hya hyx
      exact ENNReal.ofReal_le_ofReal (kernelLower a x y ht hx hy hxa hya hyx)

end CoulombEnergy

open CoulombEnergy in
theorem OMA.solution : type_of% @OMA.S_mo_326993.main := by
  intro U hOpen hConnected hBounded
  obtain ⟨a, ha⟩ := hConnected.nonempty
  obtain ⟨r, hr, hBall⟩ := Metric.isOpen_iff.mp hOpen a ha
  obtain ⟨R, hR, hU⟩ := hBounded.subset_ball_lt 0 a
  refine ⟨density a, densityNonneg a, (densityIntegrable a hR).mono_set hU, ?_⟩
  change energy a U = ⊤
  by_contra hFinite
  let c : ℝ := (Real.pi * 4 / 3) ^ 2 / 2
  let u := (energy a U).toReal
  have hc : 0 < c := by dsimp [c]; positivity
  have hu : 0 ≤ u := ENNReal.toReal_nonneg
  let t := min 1 (min r (c / (u + 1))) / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htMin : t < min 1 (min r (c / (u + 1))) := by
    dsimp [t] at ht ⊢
    linarith
  have htOne := htMin.trans_le (min_le_left _ _)
  have htr := htMin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htc := htMin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hSmall : ball a (t ^ 3) ⊆ U :=
    (ball_subset_ball (show t ^ 3 ≤ r by nlinarith [sq_nonneg t])).trans hBall
  have energyLe : energy a (ball a (t ^ 3)) ≤ energy a U :=
    (lintegral_mono fun _ => lintegral_mono_set hSmall).trans (lintegral_mono_set hSmall)
  have lower := ENNReal.toReal_mono hFinite ((energyBall a ht).trans energyLe)
  rw [ENNReal.toReal_ofReal (by positivity)] at lower
  have hlt : t * (u + 1) < c := (lt_div_iff₀ (by linarith)).mp htc
  have upper : c ≤ t * u := by
    have h : c / t ≤ u := by
      dsimp [c, u]
      convert lower using 1
      ring
    linarith [(div_le_iff₀ ht).mp h]
  nlinarith
