import FormalConjectures.WrittenOnTheWallII.GraphConjecture40

-- Reduction WrittenOnTheWallII.GraphConjecture40.conjecture40.R1 of Written on the Wall II - Conjecture 40
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1

open SimpleGraph

def H1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    1 < Fintype.card α → 2 ≤ G.pathCoverNumber →
    ⌈(((G.pathCoverNumber : ℝ) + SimpleGraph.b G + 1) / 2)⌉ ≤ G.largestInducedForestSize

def H2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    1 < Fintype.card α → G.pathCoverNumber ≤ 1 →
    ⌈(((G.pathCoverNumber : ℝ) + SimpleGraph.b G + 1) / 2)⌉ ≤ G.largestInducedForestSize

section transfer

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} {G' : SimpleGraph W}

lemma forest_set_sub (φ : G ≃g G') :
    { n | ∃ s : Finset V, (G.induce (s : Set V)).IsAcyclic ∧ s.card = n } ⊆
    { n | ∃ s : Finset W, (G'.induce (s : Set W)).IsAcyclic ∧ s.card = n } := by
  rintro n ⟨s, hs, rfl⟩
  refine ⟨s.map φ.toEquiv.toEmbedding, ?_, by simp⟩
  let ψ : G'.induce ((s.map φ.toEquiv.toEmbedding : Finset W) : Set W) →g G.induce (s : Set V) :=
    { toFun := fun x => ⟨φ.symm x.1, by
        obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp x.2
        have : φ.symm x.1 = y := by
          rw [← hxy]
          simp
        rw [this]
        exact hy⟩
      map_rel' := by
        intro a b hab
        simpa [comap_adj, φ.symm.map_adj_iff] using hab }
  refine hs.comap ψ ?_
  intro a b hab
  have : φ.symm a.1 = φ.symm b.1 := congrArg Subtype.val hab
  exact Subtype.ext (φ.symm.injective this)

lemma forest_iso (φ : G ≃g G') :
    G'.largestInducedForestSize = G.largestInducedForestSize := by
  unfold largestInducedForestSize
  congr 1
  apply Set.Subset.antisymm
  · have := forest_set_sub φ.symm
    exact this
  · exact forest_set_sub φ

lemma bip_set_sub (φ : G ≃g G') :
    { n | ∃ s : Finset V, (G.induce (s : Set V)).IsBipartite ∧ s.card = n } ⊆
    { n | ∃ s : Finset W, (G'.induce (s : Set W)).IsBipartite ∧ s.card = n } := by
  rintro n ⟨s, hs, rfl⟩
  refine ⟨s.map φ.toEquiv.toEmbedding, ?_, by simp⟩
  rw [induce_isBipartite_iff_exists_coloring] at hs ⊢
  obtain ⟨c, hc⟩ := hs
  refine ⟨fun w => c (φ.symm w), ?_⟩
  intro u hu v hv huv
  obtain ⟨u', hu', rfl⟩ := Finset.mem_map.mp hu
  obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
  have := hc u' hu' v' hv' (by simpa [φ.map_adj_iff] using huv)
  simpa using this

lemma b_iso (φ : G ≃g G') : SimpleGraph.b G' = SimpleGraph.b G := by
  unfold SimpleGraph.b largestInducedBipartiteSubgraphSize
  congr 2
  apply Set.Subset.antisymm
  · exact bip_set_sub φ.symm
  · exact bip_set_sub φ

lemma cover_set_sub (φ : G ≃g G') :
    { k | ∃ P : Finset (Finset V), P.card = k ∧ IsPathCover G P } ⊆
    { k | ∃ P : Finset (Finset W), P.card = k ∧ IsPathCover G' P } := by
  rintro k ⟨P, rfl, h1, h2, h3⟩
  let m : Finset V → Finset W := fun s => s.map φ.toEquiv.toEmbedding
  have hm : Function.Injective m := fun s t hst => Finset.map_injective _ hst
  refine ⟨P.image m, Finset.card_image_of_injective _ hm, ?_, ?_, ?_⟩
  · intro s1 hs1 s2 hs2 hne
    obtain ⟨t1, ht1, rfl⟩ := Finset.mem_image.mp hs1
    obtain ⟨t2, ht2, rfl⟩ := Finset.mem_image.mp hs2
    have : t1 ≠ t2 := fun h => hne (by rw [h])
    exact (Finset.disjoint_map _).mpr (h1 t1 ht1 t2 ht2 this)
  · intro w _
    have : φ.symm w ∈ P.biUnion id := h2 (Finset.mem_univ _)
    obtain ⟨t, ht, hwt⟩ := Finset.mem_biUnion.mp this
    refine Finset.mem_biUnion.mpr ⟨m t, Finset.mem_image_of_mem _ ht, ?_⟩
    exact Finset.mem_map.mpr ⟨φ.symm w, hwt, by simp⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨u, v, p, hp, rfl⟩ := h3 t ht
    refine ⟨φ u, φ v, p.map φ.toHom, ?_, ?_⟩
    · exact Walk.map_isPath_of_injective φ.injective hp
    · ext x
      simp only [m, Walk.support_map, List.mem_toFinset, Finset.mem_map, List.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, rfl⟩

lemma cover_iso (φ : G ≃g G') : G'.pathCoverNumber = G.pathCoverNumber := by
  unfold pathCoverNumber
  congr 1
  apply Set.Subset.antisymm
  · exact cover_set_sub φ.symm
  · exact cover_set_sub φ

end transfer

theorem main : H1 → H2 → type_of% @WrittenOnTheWallII.GraphConjecture40.conjecture40 := by
  intro h1 h2 α _ _ _ G hG hn
  classical
  let e := Fintype.equivFin α
  let φ := SimpleGraph.Iso.map e G
  have : Nontrivial (Fin (Fintype.card α)) := e.symm.nontrivial
  have hG' : (G.map e).Connected := φ.connected_iff.mp hG
  have hn' : 1 < Fintype.card (Fin (Fintype.card α)) := by simpa using hn
  rw [← forest_iso φ, ← b_iso φ, ← cover_iso φ]
  by_cases hp : 2 ≤ (G.map e).pathCoverNumber
  · exact h1 (G.map e) hG' hn' hp
  · exact h2 (G.map e) hG' hn' (by omega)

end OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1
