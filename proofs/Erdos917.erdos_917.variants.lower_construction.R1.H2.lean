import OMAReductions.R_Erdos917_erdos_917_variants_lower_construction_R1

/-!
# Proof of `Erdos917.erdos_917.variants.lower_construction.R1.H2` (Dirac's join)

The join of a `k₁`-critical graph and a `k₂`-critical graph (`3 ≤ k₁, k₂`) is `(k₁ + k₂)`-critical
and has `e₁ + e₂ + n₁ * n₂` edges.
-/

open SimpleGraph

namespace OMA.DiracJoin

/-- Disjoint union with all cross-edges between `G₁` and `G₂`. -/
def sumJoin {α β : Type*} (G₁ : SimpleGraph α) (G₂ : SimpleGraph β) : SimpleGraph (α ⊕ β) where
  Adj
    | Sum.inl u, Sum.inl v => G₁.Adj u v
    | Sum.inr u, Sum.inr v => G₂.Adj u v
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
  symm := ⟨by
    rintro (u | u) (v | v) h
    · exact G₁.symm.symm _ _ h
    · trivial
    · trivial
    · exact G₂.symm.symm _ _ h⟩
  loopless := ⟨by
    rintro (u | u) h
    · exact G₁.loopless.irrefl u h
    · exact G₂.loopless.irrefl u h⟩

lemma colorable_of_chromaticNumber_eq {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (h : G.chromaticNumber = (k : ℕ∞)) : G.Colorable k :=
  chromaticNumber_le_iff_colorable.mp h.le

lemma colorable_pred_of_lt {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (_hk : 1 ≤ k) (h : G.chromaticNumber < (k : ℕ∞)) : G.Colorable (k - 1) := by
  rw [← chromaticNumber_le_iff_colorable]
  cases hchi : G.chromaticNumber with
  | top =>
    rw [hchi] at h
    simp at h
  | coe m =>
    rw [hchi] at h
    exact mod_cast Nat.le_sub_one_of_lt (Nat.cast_lt.mp h)

lemma colorable_deleteVert {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hk : 1 ≤ k) (hcrit : G.IsCritical k) (v : V) :
    ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable (k - 1) := by
  apply colorable_pred_of_lt hk
  have h1 : ((⊤ : G.Subgraph).deleteVerts {v}).coe.chromaticNumber <
      (⊤ : G.Subgraph).coe.chromaticNumber := hcrit.2 v
  have hhom : (⊤ : G.Subgraph).coe →g G :=
    { toFun := fun x => x.1
      map_rel' := fun h => Subgraph.top_adj.mp h }
  have h2 : (⊤ : G.Subgraph).coe.chromaticNumber ≤ (k : ℕ∞) :=
    (chromaticNumber_mono_of_hom hhom).trans hcrit.1.le
  exact lt_of_lt_of_le h1 h2

lemma colorable_deleteEdge {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hk : 1 ≤ k) (hchi : G.chromaticNumber = (k : ℕ∞)) {e : Sym2 V}
    (he : G.IsCriticalEdge e) :
    (G.deleteEdges {e}).Colorable (k - 1) :=
  colorable_pred_of_lt hk (hchi ▸ he)

lemma colorable_of_fintype_equiv {V C : Type*} {G : SimpleGraph V} [Fintype C] {m : ℕ}
    (hc : G.Coloring C) (hcard : Fintype.card C = m) : G.Colorable m := by
  let e : C ≃ Fin m := Fintype.equivFinOfCardEq hcard
  exact ⟨Coloring.mk (fun v => e (hc v)) (fun hadj => e.injective.ne (hc.valid hadj))⟩

lemma sumJoin_colorable {α β : Type*} {G₁ : SimpleGraph α} {G₂ : SimpleGraph β}
    {m₁ m₂ : ℕ} (h₁ : G₁.Colorable m₁) (h₂ : G₂.Colorable m₂) :
    (sumJoin G₁ G₂).Colorable (m₁ + m₂) := by
  obtain ⟨c₁⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  refine colorable_of_fintype_equiv (C := Fin m₁ ⊕ Fin m₂) ?_ (by simp)
  refine Coloring.mk (fun x => match x with | Sum.inl u => Sum.inl (c₁ u) | Sum.inr v => Sum.inr (c₂ v)) ?_
  rintro (u | u) (v | v) hadj
  · exact Sum.inl_injective.ne (c₁.valid hadj)
  · simp
  · simp
  · exact Sum.inr_injective.ne (c₂.valid hadj)

lemma sumJoin_chromaticNumber {n₁ n₂ k₁ k₂ : ℕ}
    {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    (h₁ : G₁.chromaticNumber = (k₁ : ℕ∞)) (h₂ : G₂.chromaticNumber = (k₂ : ℕ∞)) :
    (sumJoin G₁ G₂).chromaticNumber = ((k₁ + k₂ : ℕ) : ℕ∞) := by
  apply le_antisymm
  · exact (sumJoin_colorable (colorable_of_chromaticNumber_eq h₁)
      (colorable_of_chromaticNumber_eq h₂)).chromaticNumber_le
  · rw [le_chromaticNumber_iff_coloring]
    intro m c
    let S₁ : Finset (Fin m) := Finset.univ.image (fun u : Fin n₁ => c (Sum.inl u))
    let S₂ : Finset (Fin m) := Finset.univ.image (fun v : Fin n₂ => c (Sum.inr v))
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx1
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hx2
      exact (c.valid (show (sumJoin G₁ G₂).Adj (Sum.inl u) (Sum.inr v) from trivial)) hv.symm
    have hcol₁ : G₁.Colorable S₁.card := by
      refine colorable_of_fintype_equiv (C := S₁) ?_ (Fintype.card_coe S₁)
      refine Coloring.mk (fun u => ⟨c (Sum.inl u), Finset.mem_image_of_mem _ (Finset.mem_univ u)⟩) ?_
      intro u u' hu h
      exact (c.valid (show (sumJoin G₁ G₂).Adj (Sum.inl u) (Sum.inl u') from hu))
        (congrArg Subtype.val h)
    have hcol₂ : G₂.Colorable S₂.card := by
      refine colorable_of_fintype_equiv (C := S₂) ?_ (Fintype.card_coe S₂)
      refine Coloring.mk (fun v => ⟨c (Sum.inr v), Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩) ?_
      intro v v' hv h
      exact (c.valid (show (sumJoin G₁ G₂).Adj (Sum.inr v) (Sum.inr v') from hv))
        (congrArg Subtype.val h)
    have hk₁ : k₁ ≤ S₁.card := Nat.cast_le.mp (h₁ ▸ hcol₁.chromaticNumber_le)
    have hk₂ : k₂ ≤ S₂.card := Nat.cast_le.mp (h₂ ▸ hcol₂.chromaticNumber_le)
    have hunion : S₁.card + S₂.card = (S₁ ∪ S₂).card := (Finset.card_union_of_disjoint hdisj).symm
    have hle : (S₁ ∪ S₂).card ≤ m := by
      simpa using Finset.card_le_univ (S₁ ∪ S₂)
    omega

lemma topSubgraph_lt_of_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hchi : G.chromaticNumber = (k : ℕ∞)) {v : V}
    (hcol : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable (k - 1)) (hk : 1 ≤ k) :
    ((⊤ : G.Subgraph).deleteVerts {v}).coe.chromaticNumber < (⊤ : G.Subgraph).coe.chromaticNumber := by
  have hup : ((⊤ : G.Subgraph).deleteVerts {v}).coe.chromaticNumber ≤ ((k - 1 : ℕ) : ℕ∞) :=
    hcol.chromaticNumber_le
  have hlow : ((k - 1 : ℕ) : ℕ∞) < (⊤ : G.Subgraph).coe.chromaticNumber := by
    rw [lt_chromaticNumber_iff_not_colorable]
    rintro ⟨c⟩
    have hG : G.Colorable (k - 1) :=
      ⟨Coloring.mk (fun x => c ⟨x, Set.mem_univ x⟩) (fun hadj => c.valid hadj)⟩
    have hle : k ≤ k - 1 := Nat.cast_le.mp (hchi ▸ hG.chromaticNumber_le)
    omega
  exact lt_of_le_of_lt hup hlow

lemma sumJoin_isKCritical {n₁ n₂ k₁ k₂ : ℕ}
    {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    (h₁ : Erdos917.IsKCritical G₁ k₁) (h₂ : Erdos917.IsKCritical G₂ k₂) :
    Erdos917.IsKCritical (sumJoin G₁ G₂) (k₁ + k₂) := by
  have hchi : (sumJoin G₁ G₂).chromaticNumber = ((k₁ + k₂ : ℕ) : ℕ∞) :=
    sumJoin_chromaticNumber h₁.1.1 h₂.1.1
  have hcol₁ : G₁.Colorable k₁ := colorable_of_chromaticNumber_eq h₁.1.1
  have hcol₂ : G₂.Colorable k₂ := colorable_of_chromaticNumber_eq h₂.1.1
  refine ⟨⟨hchi, ?_⟩, ?_⟩
  · rintro (u | w)
    · apply topSubgraph_lt_of_colorable hchi _ (by omega)
      obtain ⟨c₁⟩ := colorable_deleteVert hk₁ h₁.1 u
      obtain ⟨c₂⟩ := hcol₂
      refine colorable_of_fintype_equiv (C := Fin (k₁ - 1) ⊕ Fin k₂) ?_ (by simp; omega)
      refine Coloring.mk (fun x => match hx : x.1 with
        | Sum.inl y =>
          if hy : y = u then
            False.elim (x.2.2 (Set.mem_singleton_iff.mpr (hx.trans (congrArg Sum.inl hy))))
          else
            Sum.inl (c₁ ⟨y, Set.mem_univ y, fun hmem => hy (Set.mem_singleton_iff.mp hmem)⟩)
        | Sum.inr z => Sum.inr (c₂ z)) ?_
      rintro ⟨x₁ | x₁, hx⟩ ⟨y₁ | y₁, hy⟩ hadj
      · rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj] at hadj
        obtain ⟨-, hx1, -, hy1, hadj'⟩ := hadj
        have h1 : x₁ ≠ u := fun h => hx1 (Set.mem_singleton_iff.mpr (congrArg Sum.inl h))
        have h2 : y₁ ≠ u := fun h => hy1 (Set.mem_singleton_iff.mpr (congrArg Sum.inl h))
        simp only [dif_neg h1, dif_neg h2]
        have hadj1 : ((⊤ : G₁.Subgraph).deleteVerts {u}).coe.Adj
            ⟨x₁, Set.mem_univ x₁, fun hmem => h1 (Set.mem_singleton_iff.mp hmem)⟩
            ⟨y₁, Set.mem_univ y₁, fun hmem => h2 (Set.mem_singleton_iff.mp hmem)⟩ := by
          rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
          exact ⟨Set.mem_univ x₁, fun hmem => h1 (Set.mem_singleton_iff.mp hmem),
            Set.mem_univ y₁, fun hmem => h2 (Set.mem_singleton_iff.mp hmem),
            Subgraph.top_adj.mpr (Subgraph.top_adj.mp hadj')⟩
        exact Sum.inl_injective.ne (c₁.valid hadj1)
      · have h1 : x₁ ≠ u := fun h => hx.2 (Set.mem_singleton_iff.mpr (congrArg Sum.inl h))
        simp [dif_neg h1]
      · have h2 : y₁ ≠ u := fun h => hy.2 (Set.mem_singleton_iff.mpr (congrArg Sum.inl h))
        simp [dif_neg h2]
      · rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj] at hadj
        exact Sum.inr_injective.ne (c₂.valid (Subgraph.top_adj.mp hadj.2.2.2.2))
    · apply topSubgraph_lt_of_colorable hchi _ (by omega)
      obtain ⟨c₁⟩ := hcol₁
      obtain ⟨c₂⟩ := colorable_deleteVert hk₂ h₂.1 w
      refine colorable_of_fintype_equiv (C := Fin k₁ ⊕ Fin (k₂ - 1)) ?_ (by simp; omega)
      refine Coloring.mk (fun x => match hx : x.1 with
        | Sum.inl y => Sum.inl (c₁ y)
        | Sum.inr z =>
          if hz : z = w then
            False.elim (x.2.2 (Set.mem_singleton_iff.mpr (hx.trans (congrArg Sum.inr hz))))
          else
            Sum.inr (c₂ ⟨z, Set.mem_univ z, fun hmem => hz (Set.mem_singleton_iff.mp hmem)⟩)) ?_
      rintro ⟨x₁ | x₁, hx⟩ ⟨y₁ | y₁, hy⟩ hadj
      · rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj] at hadj
        exact Sum.inl_injective.ne (c₁.valid (Subgraph.top_adj.mp hadj.2.2.2.2))
      · have h2 : y₁ ≠ w := fun h => hy.2 (Set.mem_singleton_iff.mpr (congrArg Sum.inr h))
        simp [dif_neg h2]
      · have h1 : x₁ ≠ w := fun h => hx.2 (Set.mem_singleton_iff.mpr (congrArg Sum.inr h))
        simp [dif_neg h1]
      · rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj] at hadj
        obtain ⟨-, hx1, -, hy1, hadj'⟩ := hadj
        have h1 : x₁ ≠ w := fun h => hx1 (Set.mem_singleton_iff.mpr (congrArg Sum.inr h))
        have h2 : y₁ ≠ w := fun h => hy1 (Set.mem_singleton_iff.mpr (congrArg Sum.inr h))
        simp only [dif_neg h1, dif_neg h2]
        have hadj2 : ((⊤ : G₂.Subgraph).deleteVerts {w}).coe.Adj
            ⟨x₁, Set.mem_univ x₁, fun hmem => h1 (Set.mem_singleton_iff.mp hmem)⟩
            ⟨y₁, Set.mem_univ y₁, fun hmem => h2 (Set.mem_singleton_iff.mp hmem)⟩ := by
          rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
          exact ⟨Set.mem_univ x₁, fun hmem => h1 (Set.mem_singleton_iff.mp hmem),
            Set.mem_univ y₁, fun hmem => h2 (Set.mem_singleton_iff.mp hmem),
            Subgraph.top_adj.mpr (Subgraph.top_adj.mp hadj')⟩
        exact Sum.inr_injective.ne (c₂.valid hadj2)
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      change ((sumJoin G₁ G₂).deleteEdges {s(a, b)}).chromaticNumber < (sumJoin G₁ G₂).chromaticNumber
      rw [hchi]
      have hlt : (((k₁ + k₂ - 1 : ℕ) : ℕ∞)) < ((k₁ + k₂ : ℕ) : ℕ∞) := by
        exact_mod_cast (by omega : k₁ + k₂ - 1 < k₁ + k₂)
      refine lt_of_le_of_lt (Colorable.chromaticNumber_le ?_) hlt
      rcases a with u | u <;> rcases b with w | w
      · have he1 : s(u, w) ∈ G₁.edgeSet := he
        obtain ⟨c₁⟩ := colorable_deleteEdge hk₁ h₁.1.1 (h₁.2 s(u, w) he1)
        obtain ⟨c₂⟩ := hcol₂
        refine colorable_of_fintype_equiv (C := Fin (k₁ - 1) ⊕ Fin k₂) ?_ (by simp; omega)
        refine Coloring.mk (fun x => match x with | Sum.inl y => Sum.inl (c₁ y) | Sum.inr z => Sum.inr (c₂ z)) ?_
        rintro (x | x) (y | y) hadj
        · rw [deleteEdges_adj] at hadj
          have hne : s(x, y) ∉ ({s(u, w)} : Set (Sym2 (Fin n₁))) := by
            intro hmem
            apply hadj.2
            rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem ⊢
            rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl ⟨rfl, rfl⟩
            · exact Or.inr ⟨rfl, rfl⟩
          exact Sum.inl_injective.ne (c₁.valid (deleteEdges_adj.mpr ⟨hadj.1, hne⟩))
        · simp
        · simp
        · rw [deleteEdges_adj] at hadj
          exact Sum.inr_injective.ne (c₂.valid hadj.1)
      · obtain ⟨c₁⟩ := colorable_deleteVert hk₁ h₁.1 u
        obtain ⟨c₂⟩ := colorable_deleteVert hk₂ h₂.1 w
        refine colorable_of_fintype_equiv (C := Fin (k₁ - 1) ⊕ Fin (k₂ - 1) ⊕ Unit) ?_ (by simp; omega)
        refine Coloring.mk (fun x => match x with
          | Sum.inl y =>
            if hy : y = u then Sum.inr (Sum.inr ())
            else Sum.inl (c₁ ⟨y, Set.mem_univ y, fun hmem => hy (Set.mem_singleton_iff.mp hmem)⟩)
          | Sum.inr z =>
            if hz : z = w then Sum.inr (Sum.inr ())
            else Sum.inr (Sum.inl (c₂ ⟨z, Set.mem_univ z, fun hmem => hz (Set.mem_singleton_iff.mp hmem)⟩))) ?_
        rintro (x | x) (y | y) hadj
        · rw [deleteEdges_adj] at hadj
          by_cases hx : x = u <;> by_cases hy : y = u
          · subst hx hy; exact absurd rfl (G₁.ne_of_adj hadj.1)
          · simp [hx, hy]
          · simp [hx, hy]
          · simp only [dif_neg hx, dif_neg hy]
            have hadj1 : ((⊤ : G₁.Subgraph).deleteVerts {u}).coe.Adj
                ⟨x, Set.mem_univ x, fun hmem => hx (Set.mem_singleton_iff.mp hmem)⟩
                ⟨y, Set.mem_univ y, fun hmem => hy (Set.mem_singleton_iff.mp hmem)⟩ := by
              rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
              exact ⟨Set.mem_univ x, fun hmem => hx (Set.mem_singleton_iff.mp hmem),
                Set.mem_univ y, fun hmem => hy (Set.mem_singleton_iff.mp hmem),
                Subgraph.top_adj.mpr hadj.1⟩
            exact Sum.inl_injective.ne (c₁.valid hadj1)
        · rw [deleteEdges_adj] at hadj
          by_cases hx : x = u <;> by_cases hy : y = w
          · subst hx hy
            exfalso
            exact hadj.2 (Set.mem_singleton_iff.mpr rfl)
          · simp [hx, hy]
          · simp [hx, hy]
          · simp [hx, hy]
        · rw [deleteEdges_adj] at hadj
          by_cases hx : x = w <;> by_cases hy : y = u
          · subst hx hy
            exfalso
            exact hadj.2 (Set.mem_singleton_iff.mpr Sym2.eq_swap)
          · simp [hx, hy]
          · simp [hx, hy]
          · simp [hx, hy]
        · rw [deleteEdges_adj] at hadj
          by_cases hx : x = w <;> by_cases hy : y = w
          · subst hx hy; exact absurd rfl (G₂.ne_of_adj hadj.1)
          · simp [hx, hy]
          · simp [hx, hy]
          · simp only [dif_neg hx, dif_neg hy]
            have hadj2 : ((⊤ : G₂.Subgraph).deleteVerts {w}).coe.Adj
                ⟨x, Set.mem_univ x, fun hmem => hx (Set.mem_singleton_iff.mp hmem)⟩
                ⟨y, Set.mem_univ y, fun hmem => hy (Set.mem_singleton_iff.mp hmem)⟩ := by
              rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
              exact ⟨Set.mem_univ x, fun hmem => hx (Set.mem_singleton_iff.mp hmem),
                Set.mem_univ y, fun hmem => hy (Set.mem_singleton_iff.mp hmem),
                Subgraph.top_adj.mpr hadj.1⟩
            exact (Sum.inr_injective.comp Sum.inl_injective).ne (c₂.valid hadj2)
      · obtain ⟨c₁⟩ := colorable_deleteVert hk₁ h₁.1 w
        obtain ⟨c₂⟩ := colorable_deleteVert hk₂ h₂.1 u
        refine colorable_of_fintype_equiv (C := Fin (k₁ - 1) ⊕ Fin (k₂ - 1) ⊕ Unit) ?_ (by simp; omega)
        refine Coloring.mk (fun x => match x with
          | Sum.inl y =>
            if hy : y = w then Sum.inr (Sum.inr ())
            else Sum.inl (c₁ ⟨y, Set.mem_univ y, fun hmem => hy (Set.mem_singleton_iff.mp hmem)⟩)
          | Sum.inr z =>
            if hz : z = u then Sum.inr (Sum.inr ())
            else Sum.inr (Sum.inl (c₂ ⟨z, Set.mem_univ z, fun hmem => hz (Set.mem_singleton_iff.mp hmem)⟩))) ?_
        rintro (x | x) (y | y) hadj
        · rw [deleteEdges_adj] at hadj
          by_cases hx : x = w <;> by_cases hy : y = w
          · subst hx hy; exact absurd rfl (G₁.ne_of_adj hadj.1)
          · simp [hx, hy]
          · simp [hx, hy]
          · simp only [dif_neg hx, dif_neg hy]
            have hadj1 : ((⊤ : G₁.Subgraph).deleteVerts {w}).coe.Adj
                ⟨x, Set.mem_univ x, fun hmem => hx (Set.mem_singleton_iff.mp hmem)⟩
                ⟨y, Set.mem_univ y, fun hmem => hy (Set.mem_singleton_iff.mp hmem)⟩ := by
              rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
              exact ⟨Set.mem_univ x, fun hmem => hx (Set.mem_singleton_iff.mp hmem),
                Set.mem_univ y, fun hmem => hy (Set.mem_singleton_iff.mp hmem),
                Subgraph.top_adj.mpr hadj.1⟩
            exact Sum.inl_injective.ne (c₁.valid hadj1)
        · rw [deleteEdges_adj] at hadj
          by_cases hx : x = w <;> by_cases hy : y = u
          · subst hx hy
            exfalso
            exact hadj.2 (Set.mem_singleton_iff.mpr Sym2.eq_swap)
          · simp [hx, hy]
          · simp [hx, hy]
          · simp [hx, hy]
        · rw [deleteEdges_adj] at hadj
          by_cases hx : x = u <;> by_cases hy : y = w
          · subst hx hy
            exfalso
            exact hadj.2 (Set.mem_singleton_iff.mpr rfl)
          · simp [hx, hy]
          · simp [hx, hy]
          · simp [hx, hy]
        · rw [deleteEdges_adj] at hadj
          by_cases hx : x = u <;> by_cases hy : y = u
          · subst hx hy; exact absurd rfl (G₂.ne_of_adj hadj.1)
          · simp [hx, hy]
          · simp [hx, hy]
          · simp only [dif_neg hx, dif_neg hy]
            have hadj2 : ((⊤ : G₂.Subgraph).deleteVerts {u}).coe.Adj
                ⟨x, Set.mem_univ x, fun hmem => hx (Set.mem_singleton_iff.mp hmem)⟩
                ⟨y, Set.mem_univ y, fun hmem => hy (Set.mem_singleton_iff.mp hmem)⟩ := by
              rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
              exact ⟨Set.mem_univ x, fun hmem => hx (Set.mem_singleton_iff.mp hmem),
                Set.mem_univ y, fun hmem => hy (Set.mem_singleton_iff.mp hmem),
                Subgraph.top_adj.mpr hadj.1⟩
            exact (Sum.inr_injective.comp Sum.inl_injective).ne (c₂.valid hadj2)
      · have he2 : s(u, w) ∈ G₂.edgeSet := he
        obtain ⟨c₁⟩ := hcol₁
        obtain ⟨c₂⟩ := colorable_deleteEdge hk₂ h₂.1.1 (h₂.2 s(u, w) he2)
        refine colorable_of_fintype_equiv (C := Fin k₁ ⊕ Fin (k₂ - 1)) ?_ (by simp; omega)
        refine Coloring.mk (fun x => match x with | Sum.inl y => Sum.inl (c₁ y) | Sum.inr z => Sum.inr (c₂ z)) ?_
        rintro (x | x) (y | y) hadj
        · rw [deleteEdges_adj] at hadj
          exact Sum.inl_injective.ne (c₁.valid hadj.1)
        · simp
        · simp
        · rw [deleteEdges_adj] at hadj
          have hne : s(x, y) ∉ ({s(u, w)} : Set (Sym2 (Fin n₂))) := by
            intro hmem
            apply hadj.2
            rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem ⊢
            rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl ⟨rfl, rfl⟩
            · exact Or.inr ⟨rfl, rfl⟩
          exact Sum.inr_injective.ne (c₂.valid (deleteEdges_adj.mpr ⟨hadj.1, hne⟩))

lemma sym2_map_inj {α β : Type*} {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Sym2.map f) := by
  intro e₁ e₂ h
  induction e₁ using Sym2.ind with | _ a₁ b₁ =>
  induction e₂ using Sym2.ind with | _ a₂ b₂ =>
  simp only [Sym2.map_mk, Sym2.eq_iff] at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hf h1, hf h2⟩
  · exact Or.inr ⟨hf h1, hf h2⟩

lemma sumJoin_edgeSet_ncard {n₁ n₂ : ℕ}
    (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂)) :
    (sumJoin G₁ G₂).edgeSet.ncard = G₁.edgeSet.ncard + G₂.edgeSet.ncard + n₁ * n₂ := by
  let A : Set (Sym2 (Fin n₁ ⊕ Fin n₂)) := Sym2.map Sum.inl '' G₁.edgeSet
  let B : Set (Sym2 (Fin n₁ ⊕ Fin n₂)) := Sym2.map Sum.inr '' G₂.edgeSet
  let C : Set (Sym2 (Fin n₁ ⊕ Fin n₂)) :=
    (fun p : Fin n₁ × Fin n₂ => s(Sum.inl p.1, Sum.inr p.2)) '' Set.univ
  have hunion : (sumJoin G₁ G₂).edgeSet = A ∪ (B ∪ C) := by
    ext e
    constructor
    · intro he
      induction e using Sym2.ind with | _ x y =>
      rcases x with u | u <;> rcases y with v | v
      · exact Or.inl ⟨s(u, v), he, rfl⟩
      · exact Or.inr (Or.inr ⟨(u, v), trivial, rfl⟩)
      · exact Or.inr (Or.inr ⟨(v, u), trivial, Sym2.eq_swap⟩)
      · exact Or.inr (Or.inl ⟨s(u, v), he, rfl⟩)
    · rintro (⟨e₁, he₁, rfl⟩ | ⟨e₂, he₂, rfl⟩ | ⟨⟨u, v⟩, -, rfl⟩)
      · induction e₁ using Sym2.ind with | _ u v => exact he₁
      · induction e₂ using Sym2.ind with | _ u v => exact he₂
      · trivial
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro _ ⟨e₁, -, rfl⟩ ⟨e₂, -, heq⟩
    induction e₁ using Sym2.ind with | _ u v =>
    induction e₂ using Sym2.ind with | _ w z =>
    simp at heq
  have hAC : Disjoint A C := by
    rw [Set.disjoint_left]
    rintro _ ⟨e₁, -, rfl⟩ ⟨⟨w, z⟩, -, heq⟩
    induction e₁ using Sym2.ind with | _ u v =>
    simp at heq
  have hBC : Disjoint B C := by
    rw [Set.disjoint_left]
    rintro _ ⟨e₂, -, rfl⟩ ⟨⟨w, z⟩, -, heq⟩
    induction e₂ using Sym2.ind with | _ u v =>
    simp at heq
  have hA : A.ncard = G₁.edgeSet.ncard :=
    Set.ncard_image_of_injective _ (sym2_map_inj Sum.inl_injective)
  have hB : B.ncard = G₂.edgeSet.ncard :=
    Set.ncard_image_of_injective _ (sym2_map_inj Sum.inr_injective)
  have hCinj : Function.Injective (fun p : Fin n₁ × Fin n₂ => s(Sum.inl p.1, Sum.inr p.2)) := by
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ h
    simp at h
    exact Prod.ext h.1 h.2
  have hC : C.ncard = n₁ * n₂ := by
    rw [Set.ncard_image_of_injective _ hCinj, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hABC : Disjoint A (B ∪ C) := by
    rw [Set.disjoint_left]
    rintro x hxA (hxB | hxC)
    · exact Set.disjoint_left.mp hAB hxA hxB
    · exact Set.disjoint_left.mp hAC hxA hxC
  rw [hunion, Set.ncard_union_eq hABC, Set.ncard_union_eq hBC, hA, hB, hC]
  omega

lemma iso_isKCritical {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {k : ℕ} (hk : 1 ≤ k) (hcrit : Erdos917.IsKCritical G k) :
    Erdos917.IsKCritical H k := by
  have hchi : H.chromaticNumber = (k : ℕ∞) := by
    rw [le_antisymm (chromaticNumber_mono_of_hom e.symm.toHom) (chromaticNumber_mono_of_hom e.toHom),
      hcrit.1.1]
  refine ⟨⟨hchi, ?_⟩, ?_⟩
  · intro w
    apply topSubgraph_lt_of_colorable hchi _ hk
    obtain ⟨c⟩ := colorable_deleteVert hk hcrit.1 (e.symm w)
    refine ⟨Coloring.mk (fun x => c ⟨e.symm x.1, Set.mem_univ _, fun hmem => ?_⟩) ?_⟩
    · exact x.2.2 (Set.mem_singleton_iff.mpr (by
        have h := Set.mem_singleton_iff.mp hmem
        exact e.symm.injective (by simpa using h)))
    · intro x y hxy
      rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj] at hxy
      apply c.valid
      rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
      refine ⟨Set.mem_univ _,
        fun hmem => x.2.2 (Set.mem_singleton_iff.mpr (e.symm.injective (by simpa using Set.mem_singleton_iff.mp hmem))),
        Set.mem_univ _,
        fun hmem => y.2.2 (Set.mem_singleton_iff.mpr (e.symm.injective (by simpa using Set.mem_singleton_iff.mp hmem))),
        Subgraph.top_adj.mpr (e.symm.map_rel_iff.mpr (Subgraph.top_adj.mp hxy.2.2.2.2))⟩
  · intro ed hed
    induction ed using Sym2.ind with | _ w₁ w₂ =>
    change (H.deleteEdges {s(w₁, w₂)}).chromaticNumber < H.chromaticNumber
    rw [hchi]
    have hlt : ((k - 1 : ℕ) : ℕ∞) < (k : ℕ∞) := by exact_mod_cast (by omega : k - 1 < k)
    refine lt_of_le_of_lt (Colorable.chromaticNumber_le ?_) hlt
    have heG : s(e.symm w₁, e.symm w₂) ∈ G.edgeSet := e.symm.map_rel_iff.mpr hed
    obtain ⟨c⟩ := colorable_deleteEdge hk hcrit.1.1 (hcrit.2 _ heG)
    refine ⟨Coloring.mk (fun w => c (e.symm w)) ?_⟩
    intro x y hxy
    rw [deleteEdges_adj] at hxy
    apply c.valid
    rw [deleteEdges_adj]
    refine ⟨e.symm.map_rel_iff.mpr hxy.1, ?_⟩
    intro hmem
    apply hxy.2
    rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem ⊢
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨e.symm.injective h1, e.symm.injective h2⟩
    · exact Or.inr ⟨e.symm.injective h1, e.symm.injective h2⟩

lemma iso_edgeSet_ncard {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : H.edgeSet.ncard = G.edgeSet.ncard := by
  have him : H.edgeSet = Sym2.map e '' G.edgeSet := by
    ext ed
    induction ed using Sym2.ind with | _ w₁ w₂ =>
    constructor
    · intro h
      refine ⟨s(e.symm w₁, e.symm w₂), e.symm.map_rel_iff.mpr h, ?_⟩
      simp
    · rintro ⟨e', he', heq⟩
      induction e' using Sym2.ind with | _ v₁ v₂ =>
      simp only [Sym2.map_mk] at heq
      rw [← heq]
      exact e.map_rel_iff.mpr he'
  rw [him]
  exact Set.ncard_image_of_injective _ (sym2_map_inj e.injective)

end OMA.DiracJoin

theorem OMA.solution : OMA.R_Erdos917_erdos_917_variants_lower_construction_R1.H2 := by
  intro k₁ k₂ n₁ n₂ e₁ e₂ hk₁ hk₂ ⟨G₁, hG₁, he₁⟩ ⟨G₂, hG₂, he₂⟩
  let J := OMA.DiracJoin.sumJoin G₁ G₂
  let G : SimpleGraph (Fin (n₁ + n₂)) := J.comap finSumFinEquiv.symm
  let iso : J ≃g G :=
    { toEquiv := finSumFinEquiv
      map_rel_iff' := by
        intro a b
        change J.Adj (finSumFinEquiv.symm (finSumFinEquiv a))
          (finSumFinEquiv.symm (finSumFinEquiv b)) ↔ J.Adj a b
        simp }
  refine ⟨G, OMA.DiracJoin.iso_isKCritical iso (by omega)
    (OMA.DiracJoin.sumJoin_isKCritical (by omega) (by omega) hG₁ hG₂), ?_⟩
  rw [OMA.DiracJoin.iso_edgeSet_ncard iso, OMA.DiracJoin.sumJoin_edgeSet_ncard, he₁, he₂]
