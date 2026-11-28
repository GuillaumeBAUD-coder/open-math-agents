import FormalConjectures.ErdosProblems.«151»

/-! The square-root bound for clique transversals. -/

open SimpleGraph

theorem OMA.solution : type_of% @Erdos151.erdos_151.variants.sqrt_bound := by
  classical
  intro n G
  have bound (s : Finset (Fin n)) (hs : n.sqrt ≤ s.card)
      (ht : G.IsCliqueTransversal sᶜ) :
      G.cliqueTransversalNumber ≤ n - n.sqrt := by
    have hb : G.cliqueTransversalNumber ≤ sᶜ.card := csInf_le' ⟨sᶜ, ht, rfl⟩
    simp only [Finset.card_compl, Fintype.card_fin] at hb
    omega
  by_cases h : ∃ v, n.sqrt ≤ (G.neighborFinset v).card
  · obtain ⟨v, hv⟩ := h
    apply bound (G.neighborFinset v) hv
    intro t ht
    by_contra! hmiss
    have hadj : ∀ w ∈ t, G.Adj v w := fun w hw =>
      (G.mem_neighborFinset v w).mp (Finset.notMem_compl.mp (hmiss w hw))
    have hins : G.IsClique ((insert v t : Finset (Fin n)) : Set (Fin n)) := by
      simpa using ht.1.1.insert (fun w hw _ => hadj w hw)
    exact G.irrefl (hadj v (ht.1.2 hins (Finset.subset_insert v t)
      (Finset.mem_insert_self v t)))
  · push Not at h
    obtain ⟨s, hs⟩ := G.maximumIndepSet_exists
    let closed (v : Fin n) := insert v (G.neighborFinset v)
    have hcover : (Finset.univ : Finset (Fin n)) ⊆ s.biUnion closed := by
      intro w _
      by_contra hw
      have hi : G.IsIndepSet (insert w (s : Set (Fin n))) := by
        rw [← isClique_compl]
        exact ((isClique_compl (G := G)).mpr hs.isIndepSet).insert fun v hv hne =>
          ⟨hne, fun h => hw (Finset.mem_biUnion.mpr ⟨v, hv,
            Finset.mem_insert_of_mem ((G.mem_neighborFinset v w).mpr h.symm)⟩)⟩
      exact hw (Finset.mem_biUnion.mpr ⟨w,
        (hs.isMaximalIndepSet s).2 hi (Set.subset_insert _ _) (Set.mem_insert _ _),
        Finset.mem_insert_self _ _⟩)
    have hcard : n ≤ s.card * n.sqrt := by
      have hsize : n ≤ (s.biUnion closed).card := by
        simpa using Finset.card_le_card hcover
      apply hsize.trans
      apply Finset.card_biUnion_le_card_mul
      intro v _
      exact (Finset.card_insert_le v _).trans (h v)
    have hsqrt : n.sqrt ≤ s.card := by nlinarith [Nat.sqrt_le n]
    apply bound s hsqrt
    intro t ht
    obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp ht.2
    by_contra! hmiss
    exact hs.isIndepSet
      (Finset.notMem_compl.mp (hmiss a ha))
      (Finset.notMem_compl.mp (hmiss b hb)) hab (ht.1.1 ha hb hab)
