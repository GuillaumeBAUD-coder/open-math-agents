import FormalConjectures.ErdosProblems.«151»

open SimpleGraph

theorem OMA.solution : type_of% @Erdos151.erdos_151.variants.cliqueFree_three := by
  intro n G hG
  let sizes : Set ℕ :=
    {k | ∀ F : SimpleGraph (Fin n), F.CliqueFree 3 → ∃ s, F.IsNIndepSet k s}
  have existsSet {k : ℕ} (hk : k ∈ sizes) : ∃ s, G.IsNIndepSet k s := by
    change ∀ F : SimpleGraph (Fin n), F.CliqueFree 3 → ∃ s, F.IsNIndepSet k s at hk
    exact hk G hG
  have zeroMem : 0 ∈ sizes := by
    intro F _
    exact ⟨∅, by simp [isNIndepSet_iff]⟩
  have finiteSizes : sizes.Finite := (Set.finite_Iic n).subset fun k hk => by
    obtain ⟨s, hs⟩ := existsSet hk
    simpa [hs.card_eq] using Finset.card_le_univ s
  have supMem : Erdos151.H n ∈ sizes :=
    (show sizes.Nonempty from ⟨0, zeroMem⟩).csSup_mem finiteSizes
  obtain ⟨s, hs⟩ := existsSet supMem
  apply csInf_le'
  refine ⟨sᶜ, ?_, by rw [Finset.card_compl, Fintype.card_fin, hs.card_eq]⟩
  intro t ht
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp ht.2
  by_cases h : a ∈ s
  · exact ⟨b, hb, Finset.mem_compl.mpr fun hb' => hs.isIndepSet h hb' hab (ht.1.1 ha hb hab)⟩
  · exact ⟨a, ha, Finset.mem_compl.mpr h⟩
