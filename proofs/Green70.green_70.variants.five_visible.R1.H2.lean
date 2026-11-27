import OMAReductions.R_Green70_green_70_variants_five_visible_R1
import Mathlib

/-!
# Step H2 of reduction R1 of Green70.green_70.variants.five_visible

The case k = 1: any nonempty finite planar point set has a collinear singleton.
-/

open scoped Finset

theorem OMA.solution : OMA.R_Green70_green_70_variants_five_visible_R1.H2 := by
  intro P hP
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hP
  refine ⟨{a}, Finset.singleton_subset_iff.mpr ha, by simp, ?_⟩
  simpa using collinear_singleton ℝ a
