import FormalConjectures.ErdosProblems.«611»

/-! A clique of leaves with private groups of non-neighbors for the centers. -/

open Finset SimpleGraph

theorem OMA.solution : type_of% @Erdos611.erdos_611.variants.bollobas_erdos_sharp := by
  classical
  intro m hm
  have hm₁ : 1 ≤ m := by omega
  have hpre : 1 ≤ m - 1 := by omega
  have hvcard : Fintype.card (Fin m × Option (Fin (m - 1))) = m ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    rw [Nat.sub_add_cancel hm₁, pow_two]
  let e : (Fin m × Option (Fin (m - 1))) ≃ Fin (m ^ 2) :=
    Fintype.equivFinOfCardEq hvcard
  let part (v : Fin (m ^ 2)) : Fin m := (e.symm v).1
  let leaf (v : Fin (m ^ 2)) : Prop := (e.symm v).2 ≠ none
  let center (i : Fin m) : Fin (m ^ 2) := e (i, none)
  let G : SimpleGraph (Fin (m ^ 2)) := {
    Adj x y := x ≠ y ∧ ((leaf x ∧ leaf y) ∨ (part x ≠ part y ∧ (leaf x ∨ leaf y)))
    symm := ⟨by
      intro x y h
      rcases h with ⟨hne, h | h⟩
      · exact ⟨hne.symm, Or.inl ⟨h.2, h.1⟩⟩
      · exact ⟨hne.symm, Or.inr ⟨h.1.symm, h.2.symm⟩⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  have adj (x y : Fin (m ^ 2)) :
      G.Adj x y ↔ x ≠ y ∧ ((leaf x ∧ leaf y) ∨ (part x ≠ part y ∧ (leaf x ∨ leaf y))) :=
    Iff.rfl
  have center_part (i : Fin m) : part (center i) = i := by simp [part, center]
  have center_not_leaf (i : Fin m) : ¬ leaf (center i) := by simp [leaf, center]
  have eq_center (v : Fin (m ^ 2)) (hv : (e.symm v).2 = none) : center (part v) = v := by
    apply e.symm.injective
    simp only [center, Equiv.symm_apply_apply, part]
    exact Prod.ext rfl hv.symm
  have center_adj (i : Fin m) (x : Fin (m ^ 2)) :
      G.Adj (center i) x ↔ part x ≠ i ∧ leaf x := by
    rw [adj, center_part]
    have hnot := center_not_leaf i
    constructor
    · rintro ⟨_, h | ⟨hp, hl | hl⟩⟩
      · exact (hnot h.1).elim
      · exact (hnot hl).elim
      · exact ⟨hp.symm, hl⟩
    · rintro ⟨hp, hl⟩
      have hne : center i ≠ x := by
        intro h
        apply hp
        rw [← h, center_part]
      exact ⟨hne, Or.inr ⟨hp.symm, Or.inr hl⟩⟩
  let leafEmbedding : (Fin m × Fin (m - 1)) ↪ Fin (m ^ 2) :=
    ⟨fun p => e (p.1, some p.2), by
      intro p q h
      have he := e.injective h
      have hi := congrArg (fun r : Fin m × Option (Fin (m - 1)) => r.1) he
      have hj := congrArg (fun r : Fin m × Option (Fin (m - 1)) => r.2) he
      exact Prod.ext hi (Option.some.inj hj)⟩
  let leaves (I : Finset (Fin m)) : Finset (Fin (m ^ 2)) :=
    (I ×ˢ Finset.univ).map leafEmbedding
  have mem_leaves (I : Finset (Fin m)) (x : Fin (m ^ 2)) :
      x ∈ leaves I ↔ part x ∈ I ∧ leaf x := by
    constructor
    · intro hx
      obtain ⟨⟨i, j⟩, hmem, rfl⟩ := Finset.mem_map.mp hx
      have hi : i ∈ I := (Finset.mem_product.mp hmem).1
      change (e.symm (e (i, some j))).1 ∈ I ∧ (e.symm (e (i, some j))).2 ≠ none
      simpa using hi
    · rintro ⟨hpart, hleaf⟩
      rcases hxy : e.symm x with ⟨i, j⟩
      cases j with
      | none => simp [leaf, hxy] at hleaf
      | some j =>
        have hi : i ∈ I := by simpa [part, hxy] using hpart
        refine Finset.mem_map.mpr
          ⟨(i, j), Finset.mem_product.mpr ⟨hi, Finset.mem_univ _⟩, ?_⟩
        exact (congrArg e hxy).symm.trans (e.apply_symm_apply x)
  let L := leaves Finset.univ
  let K (i : Fin m) := insert (center i) (leaves (Finset.univ.erase i))
  have mem_L (x : Fin (m ^ 2)) : x ∈ L ↔ leaf x := by
    simp [L, mem_leaves]
  have mem_K (i : Fin m) (x : Fin (m ^ 2)) :
      x ∈ K i ↔ x = center i ∨ (part x ≠ i ∧ leaf x) := by
    simp [K, mem_leaves]
  have center_mem (i : Fin m) : center i ∈ K i := (mem_K i _).mpr (Or.inl rfl)
  have clique_L : G.IsClique (L : Set (Fin (m ^ 2))) := by
    intro x hx y hy hne
    exact (adj x y).mpr ⟨hne, Or.inl ⟨(mem_L x).mp hx, (mem_L y).mp hy⟩⟩
  have clique_K (i : Fin m) : G.IsClique (K i : Set (Fin (m ^ 2))) := by
    intro x hx y hy hne
    rcases (mem_K i x).mp hx with rfl | hx
    · rcases (mem_K i y).mp hy with rfl | hy
      · exact (hne rfl).elim
      · exact (center_adj i y).mpr hy
    · rcases (mem_K i y).mp hy with rfl | hy
      · exact ((center_adj i x).mpr hx).symm
      · exact (adj x y).mpr ⟨hne, Or.inl ⟨hx.2, hy.2⟩⟩
  have centered_subset {S : Finset (Fin (m ^ 2))} (hS : G.IsClique (S : Set (Fin (m ^ 2))))
      {i : Fin m} (hi : center i ∈ S) : S ⊆ K i := by
    intro x hx
    apply (mem_K i x).mpr
    by_cases he : x = center i
    · exact Or.inl he
    · exact Or.inr ((center_adj i x).mp (hS hi hx (fun h => he h.symm)))
  have maximal_K (i : Fin m) : Maximal (fun S : Finset (Fin (m ^ 2)) =>
      G.IsClique (S : Set (Fin (m ^ 2)))) (K i) := by
    refine ⟨clique_K i, ?_⟩
    intro S hS hsub
    exact centered_subset hS (hsub (center_mem i))
  have maximal_L : Maximal (fun S : Finset (Fin (m ^ 2)) =>
      G.IsClique (S : Set (Fin (m ^ 2)))) L := by
    refine ⟨clique_L, ?_⟩
    intro S hS hsub x hx
    apply (mem_L x).mpr
    intro hnot
    let i := part x
    have hi : center i ∈ S := by simpa only [i, eq_center x hnot] using hx
    let y := leafEmbedding (i, ⟨0, by omega⟩)
    have hy : y ∈ L :=
      Finset.mem_map.mpr ⟨(i, ⟨0, by omega⟩), by simp, rfl⟩
    have hpy : part y = i := by
      change (e.symm (e (i, some ⟨0, by omega⟩))).1 = i
      rw [e.symm_apply_apply]
    have hout := (mem_K i y).mp (centered_subset hS hi (hsub hy))
    rcases hout with he | he
    · exact center_not_leaf i (he ▸ (mem_L y).mp hy)
    · exact he.1 hpy
  have card_L : L.card = m * (m - 1) := by
    simp [L, leaves]
  have card_K (i : Fin m) : (K i).card = 1 + (m - 1) * (m - 1) := by
    have hnot : center i ∉ leaves (Finset.univ.erase i) := by
      intro hx
      exact center_not_leaf i ((mem_leaves _ _).mp hx).2
    simp [K, hnot, leaves, Finset.card_erase_of_mem (Finset.mem_univ i), Nat.add_comm]
  have big_L : G.IsBigMaximalClique L := by
    refine ⟨maximal_L, ?_⟩
    rw [card_L]
    exact Nat.mul_le_mul hm hpre
  have big_K (i : Fin m) : G.IsBigMaximalClique (K i) := by
    refine ⟨maximal_K i, ?_⟩
    rw [card_K]
    have hmul : 1 ≤ (m - 1) * (m - 1) := Nat.mul_le_mul hpre hpre
    omega
  have omitted (v : Fin (m ^ 2)) :
      ∃ S : Finset (Fin (m ^ 2)), G.IsBigMaximalClique S ∧ v ∉ S := by
    by_cases hv : leaf v
    · refine ⟨K (part v), big_K (part v), ?_⟩
      intro h
      rcases (mem_K (part v) v).mp h with he | he
      · exact center_not_leaf (part v) (he ▸ hv)
      · exact he.1 rfl
    · exact ⟨L, big_L, fun h => hv ((mem_L v).mp h)⟩
  refine ⟨G, ?_, ?_⟩
  · intro k hk
    obtain ⟨S, hS, rfl⟩ := hk
    by_cases h : ∃ i : Fin m, center i ∈ S
    · obtain ⟨i, hi⟩ := h
      have heq : S = K i := le_antisymm (centered_subset hS.1 hi) (hS.2 (clique_K i) (centered_subset hS.1 hi))
      rw [heq, card_K]
      push_cast [Nat.cast_sub hm₁]
      ring_nf
      exact le_rfl
    · have hsub : S ⊆ L := by
        intro x hx
        apply (mem_L x).mpr
        intro hnot
        exact h ⟨part x, by simpa only [eq_center x hnot] using hx⟩
      have heq : S = L := le_antisymm hsub (hS.2 clique_L hsub)
      rw [heq, card_L]
      push_cast [Nat.cast_sub hm₁]
      have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
  · unfold SimpleGraph.cliqueTransversalNumber
    apply le_csInf
    · refine ⟨Finset.univ.card, Finset.univ, ?_, rfl⟩
      intro S hS
      have hp : 0 < S.card := by have h := hS.2; omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hp
      exact ⟨v, hv, Finset.mem_univ v⟩
    · intro k hk
      obtain ⟨T, hT, rfl⟩ := hk
      by_contra! hsmall
      obtain ⟨v, _, hvT⟩ := hT L big_L
      obtain ⟨S, hS, hvS⟩ := omitted v
      obtain ⟨w, hwS, hwT⟩ := hT S hS
      have heq : v = w := Finset.card_le_one_iff.mp (by omega : T.card ≤ 1) hvT hwT
      exact hvS (heq.symm ▸ hwS)