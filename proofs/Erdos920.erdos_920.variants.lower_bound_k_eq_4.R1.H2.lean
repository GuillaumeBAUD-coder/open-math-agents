import OMAReductions.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1

open SimpleGraph

theorem OMA.solution : OMA.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1.H2 := by
  classical
  intro m N hN
  by_contra hnone
  have hRamsey : ∀ G : SimpleGraph (Fin N),
      completeGraph (Fin 4) ⊑ G ∨ completeGraph (Fin m) ⊑ Gᶜ := by
    intro G
    by_cases hfree : G.CliqueFree 4
    · right
      apply (not_cliqueFree_iff_top_isContained m).mp
      intro hcompl
      have hlarge : m ≤ G.indepNum :=
        Nat.le_of_not_gt fun hsmall => hnone ⟨G, hfree, hsmall⟩
      obtain ⟨s, hs⟩ := Gᶜ.exists_isNClique_cliqueNum
      exact (hcompl.mono (by simpa only [cliqueNum_compl] using hlarge)) s hs
    · exact Or.inl ((not_cliqueFree_iff_top_isContained 4).mp hfree)
  have hle : classicalRamsey 4 m ≤ N := by
    unfold classicalRamsey graphRamsey
    exact Nat.sInf_le hRamsey
  exact (not_lt_of_ge hle) hN
