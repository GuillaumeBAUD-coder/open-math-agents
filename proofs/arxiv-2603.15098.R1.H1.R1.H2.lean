import OMAReductions.R_arxiv_2603_15098_R1_H1_R1

open Set OMA.S_arxiv_2603_15098

theorem OMA.solution : OMA.R_arxiv_2603_15098_R1_H1_R1.H2 := by
  classical
  intro V M hV hc hround hres
  refine ⟨hV, hc, ?_⟩
  intro p hp
  have hpSelf := mem_connectedComponentIn hp
  by_cases hpM : p ∈ ⋃ q ∈ M, connectedComponentIn Vᶜ q
  · obtain ⟨q, hq, hpq⟩ := by simpa only [mem_iUnion] using hpM
    exact Or.inr ((connectedComponentIn_eq hpq) ▸ hround q hq)
  have hsub : connectedComponentIn Vᶜ p ⊆ Vᶜ \ ⋃ q ∈ M, connectedComponentIn Vᶜ q := by
    intro x hx
    refine ⟨connectedComponentIn_subset _ _ hx, ?_⟩
    intro hxM
    obtain ⟨q, hq, hxq⟩ := by simpa only [mem_iUnion] using hxM
    have heq := (connectedComponentIn_eq hx).trans (connectedComponentIn_eq hxq).symm
    exact hpM (mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hq, heq ▸ hpSelf⟩⟩)
  have hs := hres _ hsub isPreconnected_connectedComponentIn
  refine Or.inl ⟨p, Subset.antisymm ?_ (singleton_subset_iff.mpr hpSelf)⟩
  intro x hx
  exact mem_singleton_iff.mpr (hs hx hpSelf)