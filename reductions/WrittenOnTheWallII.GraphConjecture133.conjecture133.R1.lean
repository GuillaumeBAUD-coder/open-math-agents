import FormalConjectures.WrittenOnTheWallII.GraphConjecture133

-- Reduction WrittenOnTheWallII.GraphConjecture133.conjecture133.R1 of Written on the Wall II - Conjecture 133
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1

open SimpleGraph

def H1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    (G.radius.toNat : ℝ) + SimpleGraph.l G ≤ (SimpleGraph.path G : ℝ)

def H2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    (G.radius.toNat : ℝ) + 1 ≤ (SimpleGraph.path G : ℝ)

section transfer

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} {G' : SimpleGraph W}

lemma edist_hom_le (f : G →g G') (u v : V) : G'.edist (f u) (f v) ≤ G.edist u v := by
  by_cases h : G.edist u v = ⊤
  · rw [h]
    exact le_top
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top h
  calc G'.edist (f u) (f v) ≤ (p.map f).length := edist_le _
    _ = G.edist u v := by rw [Walk.length_map, hp]

lemma edist_iso (φ : G ≃g G') (u v : V) : G'.edist (φ u) (φ v) = G.edist u v := by
  apply le_antisymm (edist_hom_le φ.toHom u v)
  have := edist_hom_le φ.symm.toHom (φ u) (φ v)
  simpa using this

lemma radius_iso (φ : G ≃g G') : G'.radius = G.radius := by
  rw [radius_eq_iInf_iSup_edist, radius_eq_iInf_iSup_edist, ← φ.toEquiv.iInf_comp]
  congr 1
  funext u
  rw [← φ.toEquiv.iSup_comp]
  congr 1
  funext v
  exact edist_iso φ u v

lemma hasC4_iso (φ : G ≃g G') :
    (∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    (∃ a b c d : W, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G'.Adj a b ∧ G'.Adj b c ∧ G'.Adj c d ∧ G'.Adj d a) := by
  rintro ⟨a, b, c, d, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  refine ⟨φ a, φ b, φ c, φ d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact fun h => by simp_all [φ.injective.eq_iff]
    | simpa [φ.map_adj_iff]

lemma card_le_indepNeighborsCard (G : SimpleGraph V) (u : V) (S : Finset V)
    (hS : ∀ x ∈ S, G.Adj u x) (hI : G.IsIndepSet (S : Set V)) :
    S.card ≤ indepNeighborsCard G u := by
  classical
  unfold indepNeighborsCard
  let T : Finset (G.neighborSet u) := S.subtype (fun x => x ∈ G.neighborSet u)
  have hT : T.card = S.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem (fun x hx => hS x hx)
  rw [← hT]
  apply IsIndepSet.card_le_indepNum
  intro a ha b hb hab
  rw [Finset.mem_coe, Finset.mem_subtype] at ha hb
  simp only [comap_adj, Function.Embedding.subtype_apply]
  exact hI ha hb (fun h => hab (Subtype.ext h))

lemma exists_indepNeighbors (G : SimpleGraph V) (u : V) :
    ∃ S : Finset V, (∀ x ∈ S, G.Adj u x) ∧ G.IsIndepSet (S : Set V) ∧
      S.card = indepNeighborsCard G u := by
  classical
  obtain ⟨s, hs⟩ := (G.induce (G.neighborSet u)).exists_isNIndepSet_indepNum
  refine ⟨s.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hx
    exact y.2
  · intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    have := hs.isIndepSet ha' hb' (fun h => hab (by rw [h]))
    simpa [comap_adj] using this
  · rw [Finset.card_map, hs.card_eq]
    rfl

lemma indepNeighborsCard_le_iso (φ : G ≃g G') (u : V) :
    indepNeighborsCard G u ≤ indepNeighborsCard G' (φ u) := by
  obtain ⟨S, hS, hI, hc⟩ := exists_indepNeighbors G u
  rw [← hc, ← Finset.card_map φ.toEquiv.toEmbedding]
  apply card_le_indepNeighborsCard
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    simpa [φ.map_adj_iff] using hS y hy
  · intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    have := hI ha' hb' (fun h => hab (by rw [h]))
    simpa [φ.map_adj_iff] using this

lemma indepNeighborsCard_iso (φ : G ≃g G') (u : V) :
    indepNeighborsCard G' (φ u) = indepNeighborsCard G u := by
  apply le_antisymm _ (indepNeighborsCard_le_iso φ u)
  have := indepNeighborsCard_le_iso φ.symm (φ u)
  simpa using this

lemma l_iso (φ : G ≃g G') : SimpleGraph.l G' = SimpleGraph.l G := by
  unfold SimpleGraph.l averageIndepNeighbors indepNeighbors
  rw [Fintype.card_congr φ.toEquiv]
  congr 1
  symm
  apply Fintype.sum_equiv φ.toEquiv
  intro v
  simp [indepNeighborsCard_iso]

lemma path_le_iso (φ : G ≃g G') : SimpleGraph.path G ≤ SimpleGraph.path G' := by
  apply path_le_of_isInducedPath_length_le G
  intro l hl
  have h2 : G'.isInducedPath (l.map φ) := by
    refine ⟨hl.1.map φ.injective, ?_⟩
    intro i j
    have := hl.2 ⟨i.val, by simpa using i.isLt⟩ ⟨j.val, by simpa using j.isLt⟩
    simpa [List.get_eq_getElem, φ.map_adj_iff] using this
  have := length_le_path_of_isInducedPath G' _ h2
  simpa using this

lemma path_iso (φ : G ≃g G') : SimpleGraph.path G' = SimpleGraph.path G :=
  le_antisymm (path_le_iso φ.symm) (path_le_iso φ)

end transfer

theorem main : H1 → H2 → type_of% @WrittenOnTheWallII.GraphConjecture133.conjecture133 := by
  intro h1 h2 α _ _ _ G _ hG
  classical
  let e := Fintype.equivFin α
  let φ := SimpleGraph.Iso.map e G
  have : Nontrivial (Fin (Fintype.card α)) := e.symm.nontrivial
  have hG' : (G.map e).Connected := φ.connected_iff.mp hG
  have hrad : (G.map e).radius.toNat = G.radius.toNat := by rw [radius_iso φ]
  have hpath : SimpleGraph.path (G.map e) = SimpleGraph.path G := path_iso φ
  have hl : SimpleGraph.l (G.map e) = SimpleGraph.l G := l_iso φ
  intro rad hasC4 cC4
  by_cases hC : hasC4
  · have hc : cC4 = 0 := if_pos hC
    rw [hc, pow_zero]
    have := h2 (G.map e) hG' (hasC4_iso φ hC)
    rw [hrad, hpath] at this
    exact this
  · have hc : cC4 = 1 := if_neg hC
    rw [hc, pow_one]
    have hC' : ¬ (∃ a b c d : Fin (Fintype.card α), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
        c ≠ d ∧ (G.map e).Adj a b ∧ (G.map e).Adj b c ∧
        (G.map e).Adj c d ∧ (G.map e).Adj d a) :=
      fun h => hC (hasC4_iso φ.symm h)
    have := h1 (G.map e) hG' hC'
    rw [hrad, hpath, hl] at this
    exact this

end OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1
