import FormalConjectures.ErdosProblems.«151»

/-! The square-root bound for clique transversals. -/

open SimpleGraph

theorem OMA.solution : type_of% @Erdos151.erdos_151.variants.sqrt_bound := by
  classical
  intro n G
  have complement_bound (s : Finset (Fin n)) (hs : n.sqrt ≤ s.card)
      (ht : G.IsCliqueTransversal sᶜ) :
      G.cliqueTransversalNumber ≤ n - n.sqrt := by
    calc
      G.cliqueTransversalNumber ≤ sᶜ.card := csInf_le' ⟨sᶜ, ht, rfl⟩
      _ = n - s.card := by rw [Finset.card_compl, Fintype.card_fin]
      _ ≤ n - n.sqrt := Nat.sub_le_sub_left hs n
  by_cases h : ∃ v, n.sqrt ≤ (G.neighborFinset v).card
  · obtain ⟨v, hv⟩ := h
    apply complement_bound (G.neighborFinset v) hv
    intro t ht
    by_contra! hmiss
    have hadj : ∀ w ∈ t, G.Adj v w := fun w hw =>
      (G.mem_neighborFinset v w).mp (Finset.notMem_compl.mp (hmiss w hw))
    have hins : G.IsClique ((insert v t : Finset (Fin n)) : Set (Fin n)) := by
      rw [Finset.coe_insert, SimpleGraph.isClique_insert]
      exact ⟨ht.1.1, fun w hw _ => hadj w hw⟩
    exact G.irrefl (hadj v (ht.1.2 hins (Finset.subset_insert v t) (Finset.mem_insert_self v t)))
  · push Not at h
    obtain ⟨s, hs⟩ := G.maximumIndepSet_exists
    let closed (v : Fin n) := insert v (G.neighborFinset v)
    have hcover : (Finset.univ : Finset (Fin n)) ⊆ s.biUnion closed := by
      intro w _
      by_contra hw
      have hno : ∀ v ∈ s, ¬ G.Adj w v := by
        intro v hv hwv
        exact hw (Finset.mem_biUnion.mpr
          ⟨v, hv, Finset.mem_insert_of_mem ((G.mem_neighborFinset v w).mpr hwv.symm)⟩)
      have hins : G.IsIndepSet (insert w (s : Set (Fin n))) := by
        rw [← SimpleGraph.isClique_compl, SimpleGraph.isClique_insert]
        exact ⟨(SimpleGraph.isClique_compl (G := G)).mpr hs.isIndepSet,
          fun v hv hne => (G.compl_adj w v).mpr ⟨hne, hno v hv⟩⟩
      exact hw (Finset.mem_biUnion.mpr
        ⟨w, (hs.isMaximalIndepSet s).2 hins (Set.subset_insert w _) (Set.mem_insert w _),
          Finset.mem_insert_self w _⟩)
    have hcard : n ≤ s.card * n.sqrt := by
      have hsize : n ≤ (s.biUnion closed).card := by
        simpa using Finset.card_le_card hcover
      apply hsize.trans
      apply Finset.card_biUnion_le_card_mul
      intro v _
      exact (Finset.card_insert_le v _).trans (h v)
    have hsqrt : n.sqrt ≤ s.card := by
      by_contra! hlt
      exact (not_lt_of_ge ((Nat.sqrt_le n).trans hcard))
        (Nat.mul_lt_mul_of_pos_right hlt (Nat.zero_lt_of_lt hlt))
    apply complement_bound s hsqrt
    intro t ht
    obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp ht.2
    by_cases hsa : a ∈ s
    · exact ⟨b, hb, Finset.mem_compl.mpr
        (fun hsb => hs.isIndepSet hsa hsb hab (ht.1.1 ha hb hab))⟩
    · exact ⟨a, ha, Finset.mem_compl.mpr hsa⟩
