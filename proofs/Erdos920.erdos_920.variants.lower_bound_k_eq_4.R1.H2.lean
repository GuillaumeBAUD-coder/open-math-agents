import OMAReductions.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1

/-! Below the Ramsey threshold some coloring avoids both prescribed cliques. -/
open SimpleGraph

theorem OMA.solution : OMA.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1.H2 := by
  classical
  intro m N hn
  have heq : classicalRamsey 4 m =
      sInf {v : ℕ | ∀ G : SimpleGraph (Fin v), ¬(G.CliqueFree 4 ∧ Gᶜ.CliqueFree m)} := by
    simp only [classicalRamsey, graphRamsey, not_and_or, not_cliqueFree_iff_top_isContained]
  have h : ¬ ∀ G : SimpleGraph (Fin N), ¬(G.CliqueFree 4 ∧ Gᶜ.CliqueFree m) := by
    intro hh
    rw [heq] at hn
    exact hn.not_ge (Nat.sInf_le (s := {v : ℕ | ∀ G : SimpleGraph (Fin v),
      ¬(G.CliqueFree 4 ∧ Gᶜ.CliqueFree m)}) hh)
  push Not at h
  obtain ⟨G,hG,hc⟩ := h
  refine ⟨G,hG,?_⟩
  rw [← cliqueNum_compl]
  by_contra! hle
  obtain ⟨s,hs⟩ := Gᶜ.exists_isNClique_cliqueNum
  exact (CliqueFree.mono hle hc) s hs

