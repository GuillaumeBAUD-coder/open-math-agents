import OMAReductions.R_MoserWorm_mosers_worm_problem_upper_bound_R1
import Mathlib

/-! The area of the rational triangle used in the Moser worm reduction.

`{x : ℝ² | 0 ≤ x 1 ∧ |x 0| / a + x 1 / b ≤ 1}` is the triangle with vertices
`(-a, 0)`, `(a, 0)`, `(0, b)`, whose area is `a * b`. We compute the volume by Fubini:
for a fixed height `y ∈ [0, b]` the horizontal section is the interval
`[-a (1 - y / b), a (1 - y / b)]`, of length `2 a (1 - y / b)`, and
`∫_0^b 2 a (1 - y / b) dy = a * b`. -/

open MeasureTheory Set
open scoped ENNReal EuclideanGeometry

namespace WormArea

private lemma measurable_triangle {a b : ℝ} :
    MeasurableSet {x : ℝ² | 0 ≤ x 1 ∧ |x 0| / a + x 1 / b ≤ 1} := by
  have h0 : Continuous fun x : ℝ² => x 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
  have h1 : Continuous fun x : ℝ² => x 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
  have hsum : Continuous fun x : ℝ² => |x 0| / a + x 1 / b :=
    (h0.abs.div_const _).add (h1.div_const _)
  exact (isClosed_le continuous_const h1).measurableSet.inter
    (isClosed_le hsum continuous_const).measurableSet

private lemma measurable_pairs {a b : ℝ} :
    MeasurableSet {p : ℝ × ℝ | 0 ≤ p.2 ∧ |p.1| / a + p.2 / b ≤ 1} := by
  have h0 : Continuous fun p : ℝ × ℝ => p.1 := continuous_fst
  have h1 : Continuous fun p : ℝ × ℝ => p.2 := continuous_snd
  have hsum : Continuous fun p : ℝ × ℝ => |p.1| / a + p.2 / b :=
    (h0.abs.div_const _).add (h1.div_const _)
  exact (isClosed_le continuous_const h1).measurableSet.inter
    (isClosed_le hsum continuous_const).measurableSet

private lemma section_volume {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y : ℝ) :
    volume {x : ℝ | 0 ≤ y ∧ |x| / a + y / b ≤ 1} =
      if y ∈ Icc (0 : ℝ) b then ENNReal.ofReal (2 * a * (1 - y / b)) else 0 := by
  rcases le_or_gt 0 y with hy0 | hy0
  · rcases le_or_gt y b with hyb | hyb
    · rw [if_pos ⟨hy0, hyb⟩]
      have hc : 0 ≤ a * (1 - y / b) := by
        have h1 : y / b ≤ 1 := (div_le_one hb).mpr hyb
        have h2 : 0 ≤ 1 - y / b := by linarith
        exact mul_nonneg ha.le h2
      have hset : {x : ℝ | 0 ≤ y ∧ |x| / a + y / b ≤ 1}
          = Icc (-(a * (1 - y / b))) (a * (1 - y / b)) := by
        ext x
        simp only [mem_setOf_eq, mem_Icc]
        constructor
        · rintro ⟨-, hx⟩
          have h2 : |x| / a ≤ 1 - y / b := by linarith
          have h3 : |x| ≤ a * (1 - y / b) := by
            rw [div_le_iff₀ ha] at h2
            linarith
          exact abs_le.mp h3
        · rintro ⟨h1, h2⟩
          refine ⟨hy0, ?_⟩
          have h3 : |x| ≤ a * (1 - y / b) := abs_le.mpr ⟨h1, h2⟩
          have h4 : |x| / a ≤ 1 - y / b := by
            rw [div_le_iff₀ ha]
            linarith
          linarith
      rw [hset, Real.volume_Icc]
      congr 1
      ring
    · rw [if_neg (fun h => (not_le_of_gt hyb) h.2)]
      have hset : {x : ℝ | 0 ≤ y ∧ |x| / a + y / b ≤ 1} = ∅ := by
        ext x
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
        intro _
        have h1 : 1 < y / b := (one_lt_div hb).mpr hyb
        have h2 : 0 ≤ |x| / a := by positivity
        linarith
      rw [hset, measure_empty]
  · rw [if_neg (fun h => (not_le_of_gt hy0) h.1)]
    have hset : {x : ℝ | 0 ≤ y ∧ |x| / a + y / b ≤ 1} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro h
      linarith
    rw [hset, measure_empty]

private lemma volume_standard {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    volume {p : ℝ × ℝ | 0 ≤ p.2 ∧ |p.1| / a + p.2 / b ≤ 1} = ENNReal.ofReal (a * b) := by
  have hP := measurable_pairs (a := a) (b := b)
  have hfib : volume {p : ℝ × ℝ | 0 ≤ p.2 ∧ |p.1| / a + p.2 / b ≤ 1}
      = ∫⁻ y, volume {x : ℝ | 0 ≤ y ∧ |x| / a + y / b ≤ 1} := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact MeasureTheory.Measure.prod_apply_symm hP
  rw [hfib]
  have hcongr : ∫⁻ y, volume {x : ℝ | 0 ≤ y ∧ |x| / a + y / b ≤ 1}
      = ∫⁻ y, ENNReal.ofReal ((Icc (0 : ℝ) b).indicator (fun y => 2 * a * (1 - y / b)) y) := by
    apply lintegral_congr
    intro y
    rw [section_volume ha hb y]
    by_cases hy : y ∈ Icc (0 : ℝ) b
    · simp only [Set.indicator_apply, hy, if_true]
    · simp only [Set.indicator_apply, hy, if_false, ENNReal.ofReal_zero]
  rw [hcongr]
  have hind : ∫⁻ y, ENNReal.ofReal ((Icc (0 : ℝ) b).indicator (fun y => 2 * a * (1 - y / b)) y)
      = ∫⁻ y in Icc (0 : ℝ) b, ENNReal.ofReal (2 * a * (1 - y / b)) := by
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ Icc (0 : ℝ) b
    · simp only [Set.indicator_apply, hy, if_true]
    · simp only [Set.indicator_apply, hy, if_false, ENNReal.ofReal_zero]
  rw [hind]
  have hcont : Continuous fun y : ℝ => 2 * a * (1 - y / b) := by fun_prop
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) b)] fun y : ℝ => 2 * a * (1 - y / b) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have h1 : y / b ≤ 1 := (div_le_one hb).mpr hy.2
    have h2 : 0 ≤ 1 - y / b := by linarith
    have h3 : 0 ≤ a * (1 - y / b) := mul_nonneg ha.le h2
    calc 0 ≤ 2 * (a * (1 - y / b)) := by linarith
      _ = 2 * a * (1 - y / b) := by ring
  have hint : Integrable (fun y : ℝ => 2 * a * (1 - y / b)) (volume.restrict (Icc (0 : ℝ) b)) :=
    hcont.integrableOn_Icc
  have hof := ofReal_integral_eq_lintegral_ofReal hint hnonneg
  rw [← hof, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hb.le]
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) b,
      HasDerivAt (fun x : ℝ => 2 * a * x - a / b * x ^ 2) (2 * a * (1 - x / b)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => 2 * a * x) (2 * a) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * a)
    have h2 : HasDerivAt (fun x : ℝ => a / b * x ^ 2) (a / b * (2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul (a / b)
    have h3 := h1.sub h2
    have h4 : 2 * a - a / b * (2 * x) = 2 * a * (1 - x / b) := by
      field_simp
      try ring
    rw [← h4]
    exact h3
  have hInt : IntervalIntegrable (fun x : ℝ => 2 * a * (1 - x / b)) volume 0 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt]
  have hval : (2 * a * b - a / b * b ^ 2) - (2 * a * 0 - a / b * 0 ^ 2) = a * b := by
    have h1 : a / b * b ^ 2 = a * b := by
      field_simp
    rw [h1]
    ring
  rw [hval]

private theorem volume_triangle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    volume {x : ℝ² | 0 ≤ x 1 ∧ |x 0| / a + x 1 / b ≤ 1} = ENNReal.ofReal (a * b) := by
  have hT : volume {u : Fin 2 → ℝ | 0 ≤ u 1 ∧ |u 0| / a + u 1 / b ≤ 1}
      = volume {x : ℝ² | 0 ≤ x 1 ∧ |x 0| / a + x 1 / b ≤ 1} :=
    (PiLp.volume_preserving_toLp (ι := Fin 2)).measure_preimage
      (measurable_triangle (a := a) (b := b)).nullMeasurableSet
  have hP : volume {u : Fin 2 → ℝ | 0 ≤ u 1 ∧ |u 0| / a + u 1 / b ≤ 1}
      = volume {p : ℝ × ℝ | 0 ≤ p.2 ∧ |p.1| / a + p.2 / b ≤ 1} := by
    have h := (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).measure_preimage
      (measurable_pairs (a := a) (b := b)).nullMeasurableSet
    convert h using 2
    ext u
    simp [MeasurableEquiv.piFinTwo]
  rw [← hT, hP, volume_standard ha hb]

end WormArea

theorem OMA.solution : OMA.R_MoserWorm_mosers_worm_problem_upper_bound_R1.H2 := by
  show volume {x : ℝ² | 0 ≤ x 1 ∧ |x 0| / (129 / 500 : ℝ) + x 1 / (501 / 500 : ℝ) ≤ 1} =
    ENNReal.ofReal (64629 / 250000 : ℝ)
  rw [WormArea.volume_triangle (by norm_num) (by norm_num)]
  norm_num
