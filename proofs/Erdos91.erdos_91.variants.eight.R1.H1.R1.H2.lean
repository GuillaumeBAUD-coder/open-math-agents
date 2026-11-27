import OMAReductions.R_Erdos91_erdos_91_variants_eight_R1_H1_R1

-- Step Erdos91.erdos_91.variants.eight.R1.H1.R1.H2: hypothesis H2 of reduction Erdos91.erdos_91.variants.eight.R1.H1.R1
-- Credit: @OrangeHeadz
-- H2 := ∀ (p q : ℝ²) (r d : ℝ), p ≠ q → ∀ W : Finset ℝ²,     (∀ w ∈ W, dist p w = r ∧ dist q w = d) → W.card ≤ 2

-- Two circles with distinct centres in the plane meet in at most two points.
theorem OMA.solution : OMA.R_Erdos91_erdos_91_variants_eight_R1_H1_R1.H2 := by
  unfold OMA.R_Erdos91_erdos_91_variants_eight_R1_H1_R1.H2
  intro p q r d hpq W hW
  by_contra hcard
  have h3 : 2 < W.card := by omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp h3
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  have a1 : dist a p = r := by rw [dist_comm]; exact (hW a ha).1
  have b1 : dist b p = r := by rw [dist_comm]; exact (hW b hb).1
  have c1 : dist c p = r := by rw [dist_comm]; exact (hW c hc).1
  have a2 : dist a q = d := by rw [dist_comm]; exact (hW a ha).2
  have b2 : dist b q = d := by rw [dist_comm]; exact (hW b hb).2
  have c2 : dist c q = d := by rw [dist_comm]; exact (hW c hc).2
  have key : c = a ∨ c = b :=
    EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two (c₁ := p) (c₂ := q) (p₁ := a)
      (p₂ := b) (p := c) (r₁ := r) (r₂ := d) hd hpq hab a1 b1 c1 a2 b2 c2
  rcases key with h | h
  · exact hac h.symm
  · exact hbc h.symm
