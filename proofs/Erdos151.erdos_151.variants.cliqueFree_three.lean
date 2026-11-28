import FormalConjectures.ErdosProblems.«151»

theorem OMA.solution : type_of% @Erdos151.erdos_151.variants.cliqueFree_three := by
  intro n G hG
  obtain ⟨I, hI⟩ := (Nat.sSup_mem ⟨0, fun _ _ => ⟨∅, by simp, rfl⟩⟩
    ⟨n, fun k hk => let ⟨s, h⟩ := hk ⊥ (by simp); h.2 ▸ card_finset_fin_le s⟩ :
    Erdos151.H n ∈ _) G hG
  refine Nat.sInf_le ⟨Iᶜ, fun t ht => ?_, by simp [I.card_compl, hI.2]; rfl⟩
  by_contra! h
  simp at h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 ht.2
  exact hI.1 (h a ha) (h b hb) hab (ht.1.1 ha hb hab)
