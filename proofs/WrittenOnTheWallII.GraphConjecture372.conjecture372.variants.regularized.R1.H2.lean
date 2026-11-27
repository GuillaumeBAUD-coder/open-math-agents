import OMAReductions.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1

-- Step WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1.H2: hypothesis H2 of reduction WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1
-- Credit: @marcusbuffett
-- H2 := ∀ (α : Type) [Fintype α] [DecidableEq α] (T : SimpleGraph α), T.IsTree →     2 ≤ Fintype.card α →     T.vertexCoverNum.toNat ≤ 2 * T.totalDominationNumber

open SimpleGraph Finset

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1.H2 := by
  classical
  intro α _ _ T hT hn
  letI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp hn
  have hnon : {n | ∃ D : Finset α, T.IsTotalNDominatingSet n D}.Nonempty := by
    refine ⟨_, univ, ⟨?_, rfl⟩⟩
    intro x
    obtain ⟨y, hy⟩ := hT.connected.preconnected.exists_adj_of_nontrivial x
    exact ⟨y, mem_univ _, hy⟩
  obtain ⟨D, hD⟩ : ∃ D : Finset α, T.IsTotalNDominatingSet T.totalDominationNumber D :=
    Nat.sInf_mem hnon
  choose a ha hadj using hD.isTotalDominating
  -- Choose one distinct edge into D for every outside vertex.
  let E := Dᶜ.image (fun x ↦ s(x, a x))
  have hE : E ⊆ T.edgeFinset := by
    intro e he
    obtain ⟨x, _, rfl⟩ := mem_image.mp he
    simpa using hadj x
  have hcard : E.card = Dᶜ.card := by
    apply card_image_of_injOn
    intro x hx y _ h
    rcases Sym2.eq_iff.mp h with h | h
    · exact h.1
    · exact False.elim ((mem_compl.mp hx) (h.1 ▸ ha y))
  -- Adding one endpoint of each remaining edge completes a cover.
  let F := T.edgeFinset \ E
  let U := F.image (fun e ↦ e.out.1)
  have hcover : T.IsVertexCover (↑(D ∪ U) : Set α) := by
    intro x y hxy
    change x ∈ D ∪ U ∨ y ∈ D ∪ U
    by_cases he : s(x, y) ∈ E
    · obtain ⟨v, _, hv⟩ := mem_image.mp he
      rcases Sym2.eq_iff.mp hv with h | h
      · exact Or.inr (mem_union_left _ (h.2 ▸ ha v))
      · exact Or.inl (mem_union_left _ (h.2 ▸ ha v))
    · have hf : s(x, y) ∈ F := mem_sdiff.mpr ⟨by simpa using hxy, he⟩
      have hu : (s(x, y)).out.1 ∈ D ∪ U :=
        mem_union_right _ (mem_image_of_mem _ hf)
      rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(x, y)) with h | h
      · exact Or.inl (h ▸ hu)
      · exact Or.inr (h ▸ hu)
  have hbound := hcover.vertexCoverNum_le
  rw [Set.encard_coe_eq_coe_finsetCard] at hbound
  have hncover : T.vertexCoverNum.toNat ≤ (D ∪ U).card := by
    simpa using ENat.toNat_le_toNat hbound (by simp)
  have hecount := hT.card_edgeFinset
  have hpartition : F.card + E.card = T.edgeFinset.card :=
    card_sdiff_add_card_eq_card hE
  have hu : U.card ≤ F.card := card_image_le
  have hc := card_union_le D U
  have hd := hD.card_eq
  rw [hcard, card_compl] at hpartition
  omega
