import OMAReductions.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1

-- Step WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1.H2: hypothesis H2 of reduction WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1
-- Credit: @JamesSlash
-- H2 := ∀ (α : Type) [Fintype α] [DecidableEq α] (T : SimpleGraph α), T.IsTree →     2 ≤ Fintype.card α →     T.vertexCoverNum.toNat ≤ 2 * T.totalDominationNumber

--
-- Proof: take a minimum total dominating set D. Every vertex outside D has an edge into D, and
-- these edges are distinct, so at least |V| - |D| edges meet D. A tree has |V| - 1 edges, so at
-- most |D| - 1 edges avoid D. Adding one endpoint of each such edge to D gives a vertex cover of
-- size at most 2|D| - 1.

namespace OMA.WOWII372H2Claude


open SimpleGraph Finset

theorem main : ∀ (α : Type) [Fintype α] [DecidableEq α] (T : SimpleGraph α), T.IsTree →
    2 ≤ Fintype.card α →
    T.vertexCoverNum.toNat ≤ 2 * T.totalDominationNumber := by
  intro α _ _ T hT hcard
  classical
  -- every vertex has a neighbour
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hnb : ∀ v, ∃ u, T.Adj v u := fun v => hT.connected.preconnected.exists_adj_of_nontrivial v
  -- a minimum total dominating set
  have hne : {n | ∃ D : Finset α, T.IsTotalNDominatingSet n D}.Nonempty :=
    ⟨Fintype.card α, univ, ⟨fun v => by
      obtain ⟨u, hu⟩ := hnb v
      exact ⟨u, by simp, hu⟩, by simp⟩⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  have hDc : D.card = T.totalDominationNumber := hD.card_eq
  have hDdom : ∀ v, ∃ w ∈ (D : Set α), T.Adj v w := hD.isTotalDominating
  -- edges avoiding D, and edges meeting D
  set E := T.edgeFinset with hE
  set EH := E.filter (fun e => ∀ v ∈ e, v ∉ D) with hEH
  set EX := E.filter (fun e => ¬ ∀ v ∈ e, v ∉ D) with hEX
  have hsplit : EH.card + EX.card = E.card := Finset.card_filter_add_card_filter_not _
  have htree : E.card + 1 = Fintype.card α := hT.card_edgeFinset
  -- every vertex outside D owns a crossing edge
  choose w hwD hwadj using hDdom
  have hX : (univ.filter (fun v => v ∉ D)).card ≤ EX.card := by
    refine Finset.card_le_card_of_injOn (fun v => s(v, w v)) ?_ ?_
    · intro v hv
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
      simp only [hEX, coe_filter, Set.mem_ofPred_eq, hE, mem_edgeFinset, mem_edgeSet]
      refine ⟨hwadj v, ?_⟩
      intro h
      exact h (w v) (Sym2.mem_mk_right _ _) (hwD v)
    · intro a ha b hb hab
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      simp only [Sym2.eq_iff] at hab
      rcases hab with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1
      · exact absurd (h1 ▸ hwD b) ha
  have hcompl : (univ.filter (fun v => v ∉ D)).card = Fintype.card α - D.card := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
    simp
  have hDle : D.card ≤ Fintype.card α := Finset.card_le_univ D
  have hEHle : EH.card + 1 ≤ D.card := by omega
  -- the cover
  set C : Finset α := D ∪ EH.image (fun e => e.out.1) with hC
  have hcover : T.IsVertexCover (C : Set α) := by
    intro u v huv
    by_cases hu : u ∈ D
    · left; simp [hC, hu]
    by_cases hv : v ∈ D
    · right; simp [hC, hv]
    have hmem : s(u, v) ∈ EH := by
      simp only [hEH, mem_filter, hE, mem_edgeFinset, mem_edgeSet]
      refine ⟨huv, ?_⟩
      intro x hx
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact hu
      · exact hv
    have hout : (s(u, v)).out.1 ∈ C := by
      rw [hC, Finset.mem_union, Finset.mem_image]
      exact Or.inr ⟨s(u, v), hmem, rfl⟩
    rcases Sym2.mem_iff.mp (Sym2.out_fst_mem (s(u, v))) with h | h
    · left; rw [← h]; exact hout
    · right; rw [← h]; exact hout
  have hCcard : C.card ≤ D.card + EH.card :=
    (Finset.card_union_le _ _).trans (by
      have := Finset.card_image_le (s := EH) (f := fun e => e.out.1)
      omega)
  have hle : T.vertexCoverNum ≤ (C.card : ℕ∞) := by
    have := hcover.vertexCoverNum_le
    rwa [Set.encard_coe_eq_coe_finsetCard] at this
  have : T.vertexCoverNum.toNat ≤ C.card := by
    have hfin : T.vertexCoverNum ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
    exact (ENat.toNat_le_toNat hle (by simp)).trans (by simp)
  omega

end OMA.WOWII372H2Claude

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1.H2 :=
  OMA.WOWII372H2Claude.main
