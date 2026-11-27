import OMAReductions.R_Erdos1013_erdos_1013_variants_lower_R1

/-! The infimum defining h_3(k) is attained once the set is nonempty. A graph on h_3(k)
vertices with chromatic number k has at least k vertices, and its chromatic number is one
of the values whose supremum is taken; these values are bounded by the number of
vertices. -/

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_lower_R1.H3 := by
  intro k _ hex
  have hmem : sInf {n : ℕ | ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 3 ∧ G.chromaticNumber = k} ∈ {n : ℕ | ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 3 ∧ G.chromaticNumber = k} := Nat.sInf_mem hex
  obtain ⟨G, hG, hχ⟩ := hmem
  have hcard : k ≤ Erdos1013.h3 k := by
    have h := SimpleGraph.chromaticNumber_le_card (G := G)
    rw [hχ, Fintype.card_fin] at h
    exact_mod_cast h
  refine ⟨hcard, ?_⟩
  have hbdd : BddAbove {χ : ℕ | ∃ G : SimpleGraph (Fin (Erdos1013.h3 k)),
      G.CliqueFree 3 ∧ G.chromaticNumber = χ} := by
    refine ⟨Erdos1013.h3 k, ?_⟩
    rintro χ ⟨G', _, hχ'⟩
    have h := SimpleGraph.chromaticNumber_le_card (G := G')
    rw [hχ', Fintype.card_fin] at h
    exact_mod_cast h
  exact le_csSup hbdd ⟨G, hG, hχ⟩
