import OMAReductions.R_Erdos643_erdos_643_parts_ii_R1_H1_R1

/-! # The pair-shadow inequality for the whole family

Apply the hypothesis to `F = H`: the pair shadow is a subset of all `2`-subsets of `Fin n`,
of which there are `n.choose 2`. -/

theorem OMA.solution : OMA.R_Erdos643_erdos_643_parts_ii_R1_H1_R1.H2 := by
  intro n H _ hHall
  calc H.card ≤ (((Finset.univ : Finset (Fin n)).powersetCard 2).filter
        fun p => ∃ e ∈ H, p ⊆ e).card := hHall H (Finset.Subset.refl _)
    _ ≤ ((Finset.univ : Finset (Fin n)).powersetCard 2).card := Finset.card_filter_le _ _
    _ = n.choose 2 := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
