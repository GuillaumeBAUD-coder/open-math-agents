import OMAStatements.S_mo_450451
import Mathlib

open MeasureTheory Set OMA.S_mo_450451
open scoped ENNReal NNReal

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_450451.main) := by
  classical
  intro h
  let μ : Measure ℝ := Measure.dirac 0 + volume.restrict (Icc 0 1)
  have hμ : μ univ = 2 := by
    norm_num [μ, Measure.add_apply, Real.volume_Icc]
  have hfinite : IsFiniteMeasure μ := ⟨by rw [hμ]; norm_num⟩
  have hsingle : μ {0} = 1 := by
    have hs : ({0} : Set ℝ) ⊆ Icc 0 1 := singleton_subset_iff.mpr (by constructor <;> norm_num)
    simp [μ, Measure.add_apply, Measure.restrict_apply (measurableSet_singleton (0 : ℝ)),
      inter_eq_left.mpr hs]
  obtain ⟨δ, hδ, hclaim⟩ := h μ hfinite (1/4) (by norm_num)
  let r : ℝ := min (δ / 2) 1
  have hr : 0 < r := lt_min (by linarith) zero_lt_one
  have hrd : r < δ := (min_le_left _ _).trans_lt (by linarith)
  have hr1 : r ≤ 1 := min_le_right _ _
  let A := Ioc 0 r
  have hAm : MeasurableSet A := measurableSet_Ioc
  let c : ℝ≥0 := ⟨r, hr.le⟩
  have hc : c ≠ 0 := by intro h0; exact hr.ne' (congrArg (fun u : ℝ≥0 => (u : ℝ)) h0)
  have hA : μ A = (c : ℝ≥0∞) := by
    have hsub : A ⊆ Icc 0 1 := fun x hx => ⟨hx.1.le, hx.2.trans hr1⟩
    have hd : Measure.dirac (0 : ℝ) A = 0 := by
      rw [Measure.dirac_apply' _ hAm]
      simp [A]
    change (Measure.dirac (0 : ℝ) + volume.restrict (Icc 0 1)) A = _
    rw [Measure.add_apply, hd, zero_add, Measure.restrict_apply hAm, inter_eq_left.mpr hsub]
    change volume (Ioc 0 r) = _
    rw [Real.volume_Ioc, sub_zero]
    exact ENNReal.ofReal_eq_coe_nnreal hr.le
  let f : ℝ → ℝ≥0 := A.indicator (fun _ => c⁻¹)
  let g : ℝ → ℝ≥0 := ({0} : Set ℝ).indicator (fun _ => 1)
  have hfm : Measurable f := measurable_const.indicator hAm
  have hgm : Measurable g := measurable_const.indicator (measurableSet_singleton (0 : ℝ))
  have hg : ∀ x, g x ≤ 1 := by
    intro x
    by_cases hx : x = 0 <;> simp [g, hx]
  have hfc : (fun x => (f x : ℝ≥0∞)) = A.indicator (fun _ => (↑(c⁻¹) : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ A <;> simp [f, hx]
  have hgc : (fun x => (g x : ℝ≥0∞)) = ({0} : Set ℝ).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x = 0 <;> simp [g, hx]
  have hnorm : (∫⁻ x, (f x : ℝ≥0∞) ∂μ) = 1 := by
    rw [hfc, lintegral_indicator_const hAm, hA, ← ENNReal.coe_mul, inv_mul_cancel₀ hc] <;> rfl
  have hzero : (∫⁻ x, (f x : ℝ≥0∞) * (g x : ℝ≥0∞) ∂μ) = 0 := by
    have eqzero : (fun x => (f x : ℝ≥0∞) * (g x : ℝ≥0∞)) = fun _ => 0 := by
      funext x
      by_cases hx : x = 0
      · subst x
        simp [f, A]
      · simp [g, hx]
    simp [eqzero]
  have hbounds (x : ℝ) (hx : x ∈ A) :
      (2 : ℝ≥0∞)⁻¹ ≤ centeredAverage μ r g x ∧ centeredAverage μ r g x ≤ 1 := by
    have hxl : 0 < x := hx.1
    have hxr : x ≤ r := hx.2
    have hs : ({0} : Set ℝ) ⊆ Icc (x-r) (x+r) :=
      singleton_subset_iff.mpr ⟨by linarith, by linarith⟩
    have hn : (∫⁻ y in Icc (x-r) (x+r), (g y : ℝ≥0∞) ∂μ) = 1 := by
      rw [hgc, lintegral_indicator_const (measurableSet_singleton (0 : ℝ)), one_mul,
        Measure.restrict_apply (measurableSet_singleton (0 : ℝ)), inter_eq_left.mpr hs, hsingle]
    have hmass : μ (Icc (x-r) (x+r)) ≤ 2 := (measure_mono (subset_univ _)).trans_eq hμ
    have hpos : 1 ≤ μ (Icc (x-r) (x+r)) := hsingle ▸ measure_mono hs
    rw [centeredAverage, hn, one_div]
    exact ⟨ENNReal.inv_le_inv.mpr hmass, by simpa using ENNReal.inv_le_inv.mpr hpos⟩
  let value : ℝ≥0∞ := ∫⁻ x, (f x : ℝ≥0∞) * centeredAverage μ r g x ∂μ
  have hu : value ≤ 1 := calc
    value ≤ ∫⁻ x, (f x : ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ A
      · simpa using mul_le_mul_left' (hbounds x hx).2 (f x : ℝ≥0∞)
      · simp [f, hx]
    _ = 1 := hnorm
  have hl : (2 : ℝ≥0∞)⁻¹ ≤ value := calc
    _ = ∫⁻ x, (f x : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ∂μ := by
      rw [lintegral_mul_const' _ _ (by norm_num), hnorm, one_mul]
    _ ≤ value := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ A
      · exact mul_le_mul_left' (hbounds x hx).1 _
      · simp [f, hx]
  have hrange : (2 : ℝ)⁻¹ ≤ value.toReal := by
    simpa using ENNReal.toReal_mono (ne_top_of_le_ne_top (by simp) hu) hl
  have hviol := hclaim r hr hrd f g hfm hgm hnorm.le hg
  rw [hzero, ENNReal.toReal_zero, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at hviol
  change value.toReal < 1 / 4 at hviol
  norm_num at hrange
  linarith
