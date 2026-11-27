import OMAReductions.R_Green70_green_70_variants_five_visible_R1

-- Step Green70.green_70.variants.five_visible.R1.H2.
-- Credit: Hanan Beer (@hananzlt), using Codex.
-- Reduction by cosmaticdev; this proves its collinear singleton hypothesis.

theorem OMA.solution : OMA.R_Green70_green_70_variants_five_visible_R1.H2 := by
  intro P hP
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
  refine ⟨{p}, Finset.singleton_subset_iff.mpr hp, by simp, ?_⟩
  simpa using collinear_singleton ℝ p
