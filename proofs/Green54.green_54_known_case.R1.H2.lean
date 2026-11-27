import OMAReductions.R_Green54_green_54_known_case_R1
import Mathlib

open Set MeasureTheory ProbabilityTheory Green54 OMA.R_Green54_green_54_known_case_R1
open scoped Pointwise ENNReal

theorem OMA.solution : OMA.R_Green54_green_54_known_case_R1.H2 := by
  intro I A r hm hb hr
  letI : IsProbabilityMeasure gaussianMeasureInf := by unfold gaussianMeasureInf; infer_instance
  rw [← cylinder_measure I A hm] at hr
  have hmeas := hm.preimage (I.continuous_restrict (A := fun _ ↦ ℝ)).measurable
  obtain ⟨L,hLA,hL,hLr⟩ := hmeas.exists_lt_isCompact hr
  refine ⟨balancedHull ℝ L,?_,balancedHull.balanced L,
    hLr.le.trans (measure_mono (subset_balancedHull ℝ)), ?_⟩
  · have eq : balancedHull ℝ L = (Metric.closedBall (0 : ℝ) 1) • L := by
      ext x
      simp only [mem_balancedHull_iff, Set.mem_smul, Metric.mem_closedBall, dist_zero_right]
      rfl
    rw [eq]
    exact (isCompact_closedBall (0 : ℝ) 1).smul_set hL
  · rintro x hx
    obtain ⟨t,ht,y,hy,rfl⟩ := mem_balancedHull_iff.mp hx
    exact hb.smul_mem ht (hLA hy)
