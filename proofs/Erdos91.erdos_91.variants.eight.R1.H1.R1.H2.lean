import OMAReductions.R_Erdos91_erdos_91_variants_eight_R1_H1_R1

-- Step Erdos91.erdos_91.variants.eight.R1.H1.R1.H2: hypothesis H2 of reduction Erdos91.erdos_91.variants.eight.R1.H1.R1
-- Credit: @marcusbuffett
-- H2 := ∀ (p q : ℝ²) (r d : ℝ), p ≠ q → ∀ W : Finset ℝ²,     (∀ w ∈ W, dist p w = r ∧ dist q w = d) → W.card ≤ 2

theorem OMA.solution : OMA.R_Erdos91_erdos_91_variants_eight_R1_H1_R1.H2 := by
  intro p q r d hpq W hW
  by_contra! h
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp h
  simp_rw [dist_comm p, dist_comm q] at hW
  exact (EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    (by simp) hpq hab (hW a ha).1 (hW b hb).1 (hW c hc).1
    (hW a ha).2 (hW b hb).2 (hW c hc).2).elim hac.symm hbc.symm

