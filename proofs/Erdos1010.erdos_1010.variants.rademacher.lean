import FormalConjectures.ErdosProblems.«1010»
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-!
Rademacher's bound by counting triangles relative to a fixed triangle.
The count of triangles meeting the fixed triangle follows Erdős's 1964 paper
"On the number of triangles contained in certain graphs".
-/

open Finset SimpleGraph
open scoped BigOperators Classical

private theorem mantelBound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (h : G.CliqueFree 3) : G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 := by
  have hmod : Fintype.card V % 2 < 2 := Nat.mod_lt _ (by decide)
  have hbound := h.card_edgeFinset_le (r := 2)
  norm_num [Nat.choose_eq_zero_of_lt hmod] at hbound
  exact hbound.trans (Nat.div_le_div_right (Nat.sub_le _ _))

private theorem edges_le_mantel_add_triangles {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 + (G.cliqueFinset 3).card := by
  -- Delete a chosen edge from each triangle.
  have hchoose (T : {T // T ∈ G.cliqueFinset 3}) :
      ∃ a b : V, a ∈ T.val ∧ b ∈ T.val ∧ a ≠ b := by
    apply Finset.one_lt_card_iff.mp
    rw [(mem_cliqueFinset_iff.mp T.property).card_eq]
    decide
  choose a b ha hb hab using hchoose
  let removed := (G.cliqueFinset 3).attach.image (fun T => s(a T, b T))
  let H := G.deleteEdges (↑removed : Set (Sym2 V))
  have hfree : H.CliqueFree 3 := by
    intro T hT
    have hTG := IsNClique.mono (deleteEdges_le (G := G) (↑removed : Set (Sym2 V))) hT
    let T' : {T // T ∈ G.cliqueFinset 3} := ⟨T, mem_cliqueFinset_iff.mpr hTG⟩
    have hm : s(a T', b T') ∈ removed :=
      mem_image.mpr ⟨T', mem_attach _ _, rfl⟩
    have hadj : H.Adj (a T') (b T') := hT.isClique (ha T') (hb T') (hab T')
    exact (deleteEdges_adj.mp hadj).2 hm
  have hremoved : removed.card ≤ (G.cliqueFinset 3).card := by
    exact card_image_le.trans_eq card_attach
  have hH : H.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 := mantelBound H hfree
  rw [show H.edgeFinset = G.edgeFinset \ removed from edgeFinset_deleteEdges (G := G) removed] at hH
  have hpartition : G.edgeFinset.card ≤ (G.edgeFinset \ removed).card + removed.card :=
    card_le_card_sdiff_add_card
  omega

private theorem square_quarter_shift (n : ℕ) (hn : 3 ≤ n) :
    n ^ 2 / 4 + 2 = (n - 3) ^ 2 / 4 + n + n / 2 := by
  let m := (n - 3) / 2
  have hnpar : n = 2 * m + 3 ∨ n = 2 * m + 4 := by dsimp [m]; omega
  rcases hnpar with he | he
  · have hs : n - 3 = 2 * m := by omega
    have h₁ : n ^ 2 = 4 * (m ^ 2 + 3 * m + 2) + 1 := by rw [he]; ring
    have h₂ : (n - 3) ^ 2 = 4 * (m ^ 2) := by rw [hs]; ring
    rw [h₁, h₂]
    omega
  · have hs : n - 3 = 2 * m + 1 := by omega
    have h₁ : n ^ 2 = 4 * (m ^ 2 + 4 * m + 4) := by rw [he]; ring
    have h₂ : (n - 3) ^ 2 = 4 * (m ^ 2 + m) + 1 := by rw [hs]; ring
    rw [h₁, h₂]
    omega

theorem OMA.solution : type_of% @Erdos1010.erdos_1010.variants.rademacher := by
  intro n G he
  have hExists : ∃ S, G.IsNClique 3 S := by
    by_contra! h
    have hm := mantelBound G h
    simp only [Fintype.card_fin] at hm
    omega
  obtain ⟨S, hS⟩ := hExists
  let O : Finset (Fin n) := univ \ S
  have hSCard : S.card = 3 := hS.card_eq
  have hn : 3 ≤ n := by simpa [hSCard] using (card_le_univ S)
  have hOCard : O.card = n - 3 := by
    simp [O, card_sdiff_of_subset (subset_univ S), hSCard]
  have hOmem (v : Fin n) : v ∈ O ↔ v ∉ S := by simp [O]
  let D (v : Fin n) := S.filter (G.Adj v)
  have hD (v : Fin n) : D v ⊆ S := filter_subset _ _
  let edgesWithin (A : Finset (Fin n)) := G.edgeFinset.filter (fun e => e.toFinset ⊆ A)
  let edgesAcross (v : Fin n) := (D v).image (fun u => s(v, u))
  let H := G.induce (↑O : Set (Fin n))
  have hInside : (edgesWithin S).card ≤ 3 := by
    change (G.edgeFinset.filter (fun e => e.toFinset ⊆ S)).card ≤ 3
    rw [card_filter_edgeFinset_toFinset_subset]
    have h := card_edgeFinset_le_card_choose_two (G := G.induce (↑S : Set (Fin n)))
    simpa [Fintype.card_coe, hSCard] using h
  have hOutside : (edgesWithin O).card = H.edgeFinset.card :=
    card_filter_edgeFinset_toFinset_subset (G := G) O
  have hEveryEdge :
      G.edgeFinset ⊆ edgesWithin S ∪ (edgesWithin O ∪ O.biUnion edgesAcross) := by
    apply Sym2.ind
    intro u v huv
    have hadj : G.Adj u v := by simpa using huv
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · refine mem_union.mpr (.inl (mem_filter.mpr ⟨huv, ?_⟩))
      simp [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff, hu, hv]
    · apply mem_union.mpr
      right
      apply mem_union.mpr
      right
      refine mem_biUnion.mpr ⟨v, (hOmem v).mpr hv, mem_image.mpr ⟨u, ?_, Sym2.eq_swap⟩⟩
      exact mem_filter.mpr ⟨hu, hadj.symm⟩
    · apply mem_union.mpr
      right
      apply mem_union.mpr
      right
      refine mem_biUnion.mpr ⟨u, (hOmem u).mpr hu, mem_image.mpr ⟨v, ?_, rfl⟩⟩
      exact mem_filter.mpr ⟨hv, hadj⟩
    · refine mem_union.mpr (.inr (mem_union.mpr (.inl (mem_filter.mpr ⟨huv, ?_⟩))))
      simp [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff, hOmem, hu, hv]
  have hAcrossEdges : (O.biUnion edgesAcross).card ≤ ∑ v ∈ O, (D v).card := by
    refine card_biUnion_le.trans (sum_le_sum fun v _ => ?_)
    exact card_image_le
  have hEdgeCount : G.edgeFinset.card ≤ 3 + H.edgeFinset.card + ∑ v ∈ O, (D v).card := by
    have h₁ := card_le_card hEveryEdge
    have h₂ := card_union_le (edgesWithin S) (edgesWithin O ∪ O.biUnion edgesAcross)
    have h₃ := card_union_le (edgesWithin O) (O.biUnion edgesAcross)
    omega
  -- For each vertex outside S, every pair of its neighbors in S gives a triangle.
  let crossingAt (v : Fin n) := ((D v).powersetCard 2).image (insert v)
  let crossing := O.biUnion crossingAt
  have hCrossAt {v : Fin n} {T : Finset (Fin n)} (hT : T ∈ crossingAt v) :
      ∃ P, P ⊆ D v ∧ P.card = 2 ∧ insert v P = T := by
    simpa only [crossingAt, mem_image, mem_powersetCard, and_assoc] using hT
  have hDisjointAt : (↑O : Set (Fin n)).PairwiseDisjoint crossingAt := by
    intro u hu v hv huv
    refine disjoint_left.mpr fun T hTu hTv => ?_
    obtain ⟨P, _, _, hP⟩ := hCrossAt hTu
    obtain ⟨Q, hQ, _, hQT⟩ := hCrossAt hTv
    have huT : u ∈ T := hP ▸ mem_insert_self _ _
    rw [← hQT, mem_insert] at huT
    exact (hOmem u).mp hu (hD v (hQ (huT.resolve_left huv)))
  have hCrossCard (v : Fin n) (hv : v ∈ O) :
      (crossingAt v).card = (D v).card.choose 2 := by
    have hnot (P : Finset (Fin n)) (hP : P ∈ (D v).powersetCard 2) : v ∉ P :=
      fun hvP => (hOmem v).mp hv (hD v ((mem_powersetCard.mp hP).1 hvP))
    change (((D v).powersetCard 2).image (insert v)).card = _
    rw [card_image_of_injOn, card_powersetCard]
    intro P hP Q hQ heq
    have h := congrArg (fun R : Finset (Fin n) => R.erase v) heq
    simpa [erase_insert, hnot P hP, hnot Q hQ] using h
  have hCrossCount : (∑ v ∈ O, (D v).card) ≤ O.card + crossing.card := by
    change (∑ v ∈ O, (D v).card) ≤ O.card + (O.biUnion crossingAt).card
    rw [card_biUnion hDisjointAt]
    calc
      _ ≤ ∑ v ∈ O, (1 + (crossingAt v).card) := by
        apply sum_le_sum
        intro v hv
        rw [hCrossCard v hv]
        have hd : (D v).card ≤ 3 := (card_le_card (hD v)).trans_eq hSCard
        have hsmall (j : ℕ) (hj : j ≤ 3) : j ≤ 1 + j.choose 2 := by
          interval_cases j <;> decide
        exact hsmall _ hd
      _ = _ := by simp [sum_add_distrib]
  have hCrossInfo {T : Finset (Fin n)} (hT : T ∈ crossing) :
      G.IsNClique 3 T ∧ (∃ v ∈ T, v ∉ S) ∧ ∃ v ∈ T, v ∈ S := by
    obtain ⟨v, hv, hTv⟩ := mem_biUnion.mp hT
    obtain ⟨P, hP, hpCard, rfl⟩ := hCrossAt hTv
    have hPS : P ⊆ S := hP.trans (hD v)
    have hPClique : G.IsNClique 2 P :=
      ⟨hS.isClique.subset hPS, hpCard⟩
    obtain ⟨u, hu⟩ : P.Nonempty := card_pos.mp (by omega)
    exact ⟨hPClique.insert (fun u hu => (mem_filter.mp (hP hu)).2),
      ⟨v, mem_insert_self _ _, (hOmem v).mp hv⟩, ⟨u, mem_insert_of_mem hu, hPS hu⟩⟩
  -- Triangles disjoint from S are counted in the induced graph H.
  let emb : (↑O : Set (Fin n)) ↪ Fin n := Function.Embedding.subtype _
  let finsetEmb : Finset (↑O : Set (Fin n)) ↪ Finset (Fin n) := ⟨Finset.map emb, map_injective emb⟩
  let outsideTriangles := (H.cliqueFinset 3).map finsetEmb
  have hOutInfo {T : Finset (Fin n)} (hT : T ∈ outsideTriangles) :
      G.IsNClique 3 T ∧ T ⊆ O := by
    obtain ⟨P, hP, rfl⟩ := mem_map.mp hT
    refine ⟨(isNClique_induce_iff (G := G) _ _ _).mp (mem_cliqueFinset_iff.mp hP), ?_⟩
    intro v hv
    obtain ⟨w, _, rfl⟩ := mem_map.mp (show v ∈ P.map emb from hv)
    exact w.property
  have hOutCross : Disjoint outsideTriangles crossing := by
    refine disjoint_left.mpr fun T hout hcross => ?_
    obtain ⟨v, hv, hvS⟩ := (hCrossInfo hcross).2.2
    exact (hOmem v).mp ((hOutInfo hout).2 hv) hvS
  have hSnot : S ∉ outsideTriangles ∪ crossing := by
    intro h
    rcases mem_union.mp h with hout | hcross
    · obtain ⟨v, hv⟩ : S.Nonempty := card_pos.mp (by omega)
      exact (hOmem v).mp ((hOutInfo hout).2 hv) hv
    · obtain ⟨v, hv, hvS⟩ := (hCrossInfo hcross).2.1
      exact hvS hv
  have hTriCount :
      (H.cliqueFinset 3).card + crossing.card + 1 ≤ (G.cliqueFinset 3).card := by
    have hsub : insert S (outsideTriangles ∪ crossing) ⊆ G.cliqueFinset 3 := by
      intro T hT
      apply mem_cliqueFinset_iff.mpr
      rcases mem_insert.mp hT with rfl | hT
      · exact hS
      rcases mem_union.mp hT with hout | hcross
      · exact (hOutInfo hout).1
      · exact (hCrossInfo hcross).1
    have h := card_le_card hsub
    rw [card_insert_of_notMem hSnot, card_union_of_disjoint hOutCross] at h
    simpa [outsideTriangles] using h
  have hH := edges_le_mantel_add_triangles H
  have hOType : Fintype.card (↑O : Set (Fin n)) = n - 3 := (Fintype.card_coe O).trans hOCard
  rw [hOType] at hH
  have hshift := square_quarter_shift n hn
  omega