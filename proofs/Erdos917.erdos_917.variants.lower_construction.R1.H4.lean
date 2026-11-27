import OMAReductions.R_Erdos917_erdos_917_variants_lower_construction_R1

/-!
# Proof of `Erdos917.erdos_917.variants.lower_construction.R1.H4` (Toft's 5-critical graph)

Given a `4`-critical graph `G₁` on `n₁` vertices and a `3`-critical graph `G₂` on `n₂` vertices,
Toft's graph `T(G₁, G₂)` takes `G₁` on `A`, an independent copy `B` matched to `A`, `G₂` on `C`,
and all cross-edges between `B` and `C`. It is `5`-critical and has `e₁ + e₂ + n₁ + n₁ * n₂`
edges.
-/

open SimpleGraph

namespace OMA.Toft5

/-- Vertex set `A ⊔ B ⊔ C` of Toft's `5`-critical construction. -/
abbrev V (n₁ n₂ : ℕ) := (Fin n₁ ⊕ Fin n₁) ⊕ Fin n₂

/-- Toft's `5`-critical graph `T(G₁, G₂)` on `(Fin n₁ ⊕ Fin n₁) ⊕ Fin n₂`. -/
def toft5 {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂)) :
    SimpleGraph (V n₁ n₂) where
  Adj
    | Sum.inl (Sum.inl u), Sum.inl (Sum.inl v) => G₁.Adj u v
    | Sum.inl (Sum.inl u), Sum.inl (Sum.inr v) => u = v
    | Sum.inl (Sum.inr u), Sum.inl (Sum.inl v) => u = v
    | Sum.inl (Sum.inr _), Sum.inr _ => True
    | Sum.inr _, Sum.inl (Sum.inr _) => True
    | Sum.inr u, Sum.inr v => G₂.Adj u v
    | _, _ => False
  symm := ⟨by
    rintro ((u | u) | u) ((v | v) | v) h <;>
      first | exact h | exact h.symm⟩
  loopless := ⟨by
    rintro ((u | u) | u) h <;>
      first | exact h | exact G₁.loopless.irrefl u h | exact G₂.loopless.irrefl u h⟩

lemma colorable_of_chromaticNumber_eq {W : Type*} {G : SimpleGraph W} {k : ℕ}
    (h : G.chromaticNumber = (k : ℕ∞)) : G.Colorable k :=
  chromaticNumber_le_iff_colorable.mp h.le

lemma colorable_pred_of_lt {W : Type*} {G : SimpleGraph W} {k : ℕ}
    (_hk : 1 ≤ k) (h : G.chromaticNumber < (k : ℕ∞)) : G.Colorable (k - 1) := by
  rw [← chromaticNumber_le_iff_colorable]
  cases hchi : G.chromaticNumber with
  | top =>
    rw [hchi] at h
    simp at h
  | coe m =>
    rw [hchi] at h
    exact mod_cast Nat.le_sub_one_of_lt (Nat.cast_lt.mp h)

lemma colorable_deleteVert {W : Type*} {G : SimpleGraph W} {k : ℕ}
    (hk : 1 ≤ k) (hcrit : G.IsCritical k) (v : W) :
    ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable (k - 1) := by
  apply colorable_pred_of_lt hk
  have h1 : ((⊤ : G.Subgraph).deleteVerts {v}).coe.chromaticNumber <
      (⊤ : G.Subgraph).coe.chromaticNumber := hcrit.2 v
  have hhom : (⊤ : G.Subgraph).coe →g G :=
    { toFun := fun x => x.1
      map_rel' := fun h => Subgraph.top_adj.mp h }
  exact lt_of_lt_of_le h1 ((chromaticNumber_mono_of_hom hhom).trans hcrit.1.le)

lemma colorable_deleteEdge {W : Type*} {G : SimpleGraph W} {k : ℕ}
    (hk : 1 ≤ k) (hchi : G.chromaticNumber = (k : ℕ∞)) {e : Sym2 W}
    (he : G.IsCriticalEdge e) :
    (G.deleteEdges {e}).Colorable (k - 1) :=
  colorable_pred_of_lt hk (hchi ▸ he)

lemma colorable_of_fintype_equiv {W C : Type*} {G : SimpleGraph W} [Fintype C] {m : ℕ}
    (hc : G.Coloring C) (hcard : Fintype.card C = m) : G.Colorable m := by
  let e : C ≃ Fin m := Fintype.equivFinOfCardEq hcard
  exact ⟨Coloring.mk (fun v => e (hc v)) (fun hadj => e.injective.ne (hc.valid hadj))⟩

lemma isKCritical_of_edgeCritical_of_no_isolated {W : Type*} {G : SimpleGraph W} {k : ℕ}
    (hchi : G.chromaticNumber = (k : ℕ∞))
    (hedge : ∀ e ∈ G.edgeSet, G.IsCriticalEdge e)
    (hdeg : ∀ v : W, ∃ w : W, G.Adj v w) :
    Erdos917.IsKCritical G k := by
  refine ⟨⟨hchi, ?_⟩, hedge⟩
  intro v
  obtain ⟨w, hw⟩ := hdeg v
  have hhom₁ : ((⊤ : G.Subgraph).deleteVerts {v}).coe →g G.deleteEdges {s(v, w)} :=
    { toFun := fun x => x.1
      map_rel' := by
        intro x y hxy
        rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj] at hxy
        rw [deleteEdges_adj]
        refine ⟨Subgraph.top_adj.mp hxy.2.2.2.2, ?_⟩
        intro hmem
        rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
        rcases hmem with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact hxy.2.1 (Set.mem_singleton_iff.mpr h1)
        · exact hxy.2.2.2.1 (Set.mem_singleton_iff.mpr h2) }
  have hhom₂ : G →g (⊤ : G.Subgraph).coe :=
    { toFun := fun x => ⟨x, Set.mem_univ x⟩
      map_rel' := fun h => Subgraph.top_adj.mpr h }
  exact lt_of_le_of_lt (chromaticNumber_mono_of_hom hhom₁)
    (lt_of_lt_of_le (hedge s(v, w) hw) (chromaticNumber_mono_of_hom hhom₂))

lemma toft5_colorable5 {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    (h₁ : G₁.Colorable 4) (h₂ : G₂.Colorable 3) :
    (toft5 G₁ G₂).Colorable 5 := by
  obtain ⟨c₁⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  refine ⟨Coloring.mk (fun x => match x with
    | Sum.inl (Sum.inl u) => (c₁ u).castSucc
    | Sum.inl (Sum.inr _) => 4
    | Sum.inr w => (c₂ w).castSucc.castSucc) ?_⟩
  rintro ((u | u) | u) ((v | v) | v) hadj
  · exact (Fin.castSucc_injective 4).ne (c₁.valid hadj)
  · exact (Fin.castSucc_lt_last (c₁ u)).ne
  · simp [toft5] at hadj
  · exact (Fin.castSucc_lt_last (c₁ v)).ne.symm
  · simp [toft5] at hadj
  · have hlt : ((c₂ v).castSucc.castSucc : Fin 5).val < 4 := by
      have := (c₂ v).isLt; simp; omega
    exact Fin.ext_iff.not.mpr (by simp; omega)
  · simp [toft5] at hadj
  · have hlt : ((c₂ u).castSucc.castSucc : Fin 5).val < 4 := by
      have := (c₂ u).isLt; simp; omega
    exact Fin.ext_iff.not.mpr (by simp; omega)
  · exact ((Fin.castSucc_injective 4).comp (Fin.castSucc_injective 3)).ne (c₂.valid hadj)

lemma drop_color {k : ℕ} (col : Fin k) (x y : Fin k)
    (hx : x ≠ col) (hy : y ≠ col) (hxy : x ≠ y) :
    (⟨if x.val < col.val then x.val else x.val - 1, by
      have := x.isLt; have := col.isLt; split_ifs <;> omega⟩ : Fin (k - 1)) ≠
    ⟨if y.val < col.val then y.val else y.val - 1, by
      have := y.isLt; have := col.isLt; split_ifs <;> omega⟩ := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only at hv
  have h1 : x.val ≠ col.val := fun e => hx (Fin.ext e)
  have h2 : y.val ≠ col.val := fun e => hy (Fin.ext e)
  apply hxy
  apply Fin.ext
  split_ifs at hv <;> omega

lemma toft5_not_colorable4 {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    (hn₁ : 0 < n₁)
    (hchi₁ : G₁.chromaticNumber = (4 : ℕ∞)) (hchi₂ : G₂.chromaticNumber = (3 : ℕ∞)) :
    ¬ (toft5 G₁ G₂).Colorable 4 := by
  rintro ⟨c⟩
  let SB : Finset (Fin 4) := Finset.univ.image (fun i : Fin n₁ => c (Sum.inl (Sum.inr i)))
  let SC : Finset (Fin 4) := Finset.univ.image (fun j : Fin n₂ => c (Sum.inr j))
  have hdisj : Disjoint SB SC := by
    rw [Finset.disjoint_left]
    intro x hxB hxC
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxB
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hxC
    exact (c.valid (show (toft5 G₁ G₂).Adj (Sum.inl (Sum.inr i)) (Sum.inr j) from trivial)) hj.symm
  have hBpos : 0 < SB.card := Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, hn₁⟩)⟩
  have hcolC : G₂.Colorable SC.card := by
    refine colorable_of_fintype_equiv (C := SC) ?_ (Fintype.card_coe SC)
    refine Coloring.mk (fun j => ⟨c (Sum.inr j), Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩) ?_
    intro j j' hjj h
    exact (c.valid (show (toft5 G₁ G₂).Adj (Sum.inr j) (Sum.inr j') from hjj)) (congrArg Subtype.val h)
  have hCge : 3 ≤ SC.card := Nat.cast_le.mp (hchi₂ ▸ hcolC.chromaticNumber_le)
  have hsum : SB.card + SC.card ≤ 4 := by
    have h1 : SB.card + SC.card = (SB ∪ SC).card := (Finset.card_union_of_disjoint hdisj).symm
    have h2 : (SB ∪ SC).card ≤ 4 := by simpa using Finset.card_le_univ (SB ∪ SC)
    omega
  have hB1 : SB.card = 1 := by omega
  obtain ⟨col, hcol⟩ := Finset.card_eq_one.mp hB1
  have hB : ∀ i : Fin n₁, c (Sum.inl (Sum.inr i)) = col := fun i =>
    Finset.mem_singleton.mp (hcol ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hA : ∀ i : Fin n₁, c (Sum.inl (Sum.inl i)) ≠ col := fun i => by
    rw [← hB i]
    exact c.valid (show (toft5 G₁ G₂).Adj (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inr i)) from rfl)
  have hcol3 : G₁.Colorable 3 :=
    ⟨Coloring.mk (fun i =>
      ⟨if (c (Sum.inl (Sum.inl i))).val < col.val then (c (Sum.inl (Sum.inl i))).val
       else (c (Sum.inl (Sum.inl i))).val - 1, by
        have := (c (Sum.inl (Sum.inl i))).isLt; have := col.isLt; split_ifs <;> omega⟩)
      fun {i i'} hii => drop_color col _ _ (hA i) (hA i') (c.valid hii)⟩
  have hle : (4 : ℕ∞) ≤ (3 : ℕ∞) := hchi₁ ▸ hcol3.chromaticNumber_le
  norm_num at hle

lemma toft5_delete_A {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    {u v : Fin n₁} (h₁ : (G₁.deleteEdges {s(u, v)}).Colorable 3) (h₂ : G₂.Colorable 3) :
    ((toft5 G₁ G₂).deleteEdges {s(Sum.inl (Sum.inl u), Sum.inl (Sum.inl v))}).Colorable 4 := by
  obtain ⟨c₁⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  refine ⟨Coloring.mk (fun x => match x with
    | Sum.inl (Sum.inl y) => (c₁ y).castSucc
    | Sum.inl (Sum.inr _) => 3
    | Sum.inr z => (c₂ z).castSucc) ?_⟩
  rintro ((x | x) | x) ((y | y) | y) hadj
  · rw [deleteEdges_adj] at hadj
    have hne : s(x, y) ∉ ({s(u, v)} : Set (Sym2 (Fin n₁))) := by
      intro hmem
      apply hadj.2
      rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem ⊢
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    exact (Fin.castSucc_injective 3).ne (c₁.valid (deleteEdges_adj.mpr ⟨hadj.1, hne⟩))
  · exact (Fin.castSucc_lt_last (c₁ x)).ne
  · simp [deleteEdges_adj, toft5] at hadj
  · exact (Fin.castSucc_lt_last (c₁ y)).ne.symm
  · simp [deleteEdges_adj, toft5] at hadj
  · exact (Fin.castSucc_lt_last (c₂ y)).ne.symm
  · simp [deleteEdges_adj, toft5] at hadj
  · exact (Fin.castSucc_lt_last (c₂ x)).ne
  · rw [deleteEdges_adj] at hadj
    exact (Fin.castSucc_injective 3).ne (c₂.valid hadj.1)

lemma ne_flip4 (a : Fin 4) : a ≠ if a = 2 then 3 else 2 := by
  fin_cases a <;> decide

lemma toft5_delete_C {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    {u v : Fin n₂} (h₁ : G₁.Colorable 4) (h₂ : (G₂.deleteEdges {s(u, v)}).Colorable 2) :
    ((toft5 G₁ G₂).deleteEdges {s(Sum.inr u, Sum.inr v)}).Colorable 4 := by
  obtain ⟨c₁⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  refine ⟨Coloring.mk (fun x => match x with
    | Sum.inl (Sum.inl y) => c₁ y
    | Sum.inl (Sum.inr y) => if c₁ y = 2 then 3 else 2
    | Sum.inr z => (c₂ z).castSucc.castSucc) ?_⟩
  rintro ((x | x) | x) ((y | y) | y) hadj
  · rw [deleteEdges_adj] at hadj
    exact c₁.valid hadj.1
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    exact ne_flip4 (c₁ x)
  · simp [deleteEdges_adj, toft5] at hadj
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    exact (ne_flip4 (c₁ x)).symm
  · simp [deleteEdges_adj, toft5] at hadj
  · have := (c₂ y).isLt
    change (if c₁ x = 2 then (3 : Fin 4) else 2) ≠ (c₂ y).castSucc.castSucc
    split_ifs <;> exact Fin.ext_iff.not.mpr (by simp; omega)
  · simp [deleteEdges_adj, toft5] at hadj
  · have := (c₂ x).isLt
    change (c₂ x).castSucc.castSucc ≠ if c₁ y = 2 then (3 : Fin 4) else 2
    split_ifs <;> exact Fin.ext_iff.not.mpr (by simp; omega)
  · rw [deleteEdges_adj] at hadj
    have hne : s(x, y) ∉ ({s(u, v)} : Set (Sym2 (Fin n₂))) := by
      intro hmem
      apply hadj.2
      rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem ⊢
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    exact ((Fin.castSucc_injective 3).comp (Fin.castSucc_injective 2)).ne
      (c₂.valid (deleteEdges_adj.mpr ⟨hadj.1, hne⟩))

lemma toft5_delete_match {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    {u : Fin n₁}
    (h₁ : ((⊤ : G₁.Subgraph).deleteVerts {u}).coe.Colorable 3) (h₂ : G₂.Colorable 3) :
    ((toft5 G₁ G₂).deleteEdges {s(Sum.inl (Sum.inl u), Sum.inl (Sum.inr u))}).Colorable 4 := by
  obtain ⟨c₁⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  refine ⟨Coloring.mk (fun x => match x with
    | Sum.inl (Sum.inl y) =>
      if hy : y = u then 3
      else (c₁ ⟨y, Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm)⟩).castSucc
    | Sum.inl (Sum.inr _) => 3
    | Sum.inr z => (c₂ z).castSucc) ?_⟩
  rintro ((x | x) | x) ((y | y) | y) hadj
  · rw [deleteEdges_adj] at hadj
    by_cases hx : x = u <;> by_cases hy : y = u
    · subst hx hy; exact absurd rfl (G₁.ne_of_adj hadj.1)
    · simp only [dif_pos hx, dif_neg hy]
      exact (Fin.castSucc_lt_last _).ne.symm
    · simp only [dif_neg hx, dif_pos hy]
      exact (Fin.castSucc_lt_last _).ne
    · simp only [dif_neg hx, dif_neg hy]
      have hadj1 : ((⊤ : G₁.Subgraph).deleteVerts {u}).coe.Adj
          ⟨x, Set.mem_univ x, fun hm => hx (Set.mem_singleton_iff.mp hm)⟩
          ⟨y, Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm)⟩ := by
        rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
        exact ⟨Set.mem_univ x, fun hm => hx (Set.mem_singleton_iff.mp hm),
          Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm),
          Subgraph.top_adj.mpr hadj.1⟩
      exact (Fin.castSucc_injective 3).ne (c₁.valid hadj1)
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    by_cases hx : x = u
    · subst hx; exfalso; exact hadj.2 (Set.mem_singleton_iff.mpr rfl)
    · simp only [dif_neg hx]
      exact (Fin.castSucc_lt_last _).ne
  · simp [deleteEdges_adj, toft5] at hadj
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    by_cases hx : x = u
    · subst hx; exfalso; exact hadj.2 (Set.mem_singleton_iff.mpr Sym2.eq_swap)
    · simp only [dif_neg hx]
      exact (Fin.castSucc_lt_last _).ne.symm
  · simp [deleteEdges_adj, toft5] at hadj
  · exact (Fin.castSucc_lt_last (c₂ y)).ne.symm
  · simp [deleteEdges_adj, toft5] at hadj
  · exact (Fin.castSucc_lt_last (c₂ x)).ne
  · rw [deleteEdges_adj] at hadj
    exact (Fin.castSucc_injective 3).ne (c₂.valid hadj.1)

lemma toft5_delete_cross {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    {u : Fin n₁} {w : Fin n₂}
    (h₁ : ((⊤ : G₁.Subgraph).deleteVerts {u}).coe.Colorable 3)
    (h₂ : ((⊤ : G₂.Subgraph).deleteVerts {w}).coe.Colorable 2) :
    ((toft5 G₁ G₂).deleteEdges {s(Sum.inl (Sum.inr u), Sum.inr w)}).Colorable 4 := by
  obtain ⟨c₁⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  refine ⟨Coloring.mk (fun x => match x with
    | Sum.inl (Sum.inl y) =>
      if hy : y = u then 3
      else (c₁ ⟨y, Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm)⟩).castSucc
    | Sum.inl (Sum.inr y) => if y = u then 0 else 3
    | Sum.inr z =>
      if hz : z = w then 0
      else (c₂ ⟨z, Set.mem_univ z, fun hm => hz (Set.mem_singleton_iff.mp hm)⟩).succ.castSucc) ?_⟩
  rintro ((x | x) | x) ((y | y) | y) hadj
  · rw [deleteEdges_adj] at hadj
    by_cases hx : x = u <;> by_cases hy : y = u
    · subst hx hy; exact absurd rfl (G₁.ne_of_adj hadj.1)
    · simp only [dif_pos hx, dif_neg hy]
      exact (Fin.castSucc_lt_last _).ne.symm
    · simp only [dif_neg hx, dif_pos hy]
      exact (Fin.castSucc_lt_last _).ne
    · simp only [dif_neg hx, dif_neg hy]
      have hadj1 : ((⊤ : G₁.Subgraph).deleteVerts {u}).coe.Adj
          ⟨x, Set.mem_univ x, fun hm => hx (Set.mem_singleton_iff.mp hm)⟩
          ⟨y, Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm)⟩ := by
        rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
        exact ⟨Set.mem_univ x, fun hm => hx (Set.mem_singleton_iff.mp hm),
          Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm),
          Subgraph.top_adj.mpr hadj.1⟩
      exact (Fin.castSucc_injective 3).ne (c₁.valid hadj1)
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    by_cases hx : x = u
    · simp [hx]
    · simp only [dif_neg hx, if_neg hx]
      exact (Fin.castSucc_lt_last _).ne
  · simp [deleteEdges_adj, toft5] at hadj
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    by_cases hx : x = u
    · simp [hx]
    · simp only [dif_neg hx, if_neg hx]
      exact (Fin.castSucc_lt_last _).ne.symm
  · simp [deleteEdges_adj, toft5] at hadj
  · rw [deleteEdges_adj] at hadj
    by_cases hx : x = u <;> by_cases hy : y = w
    · subst hx hy; exfalso; exact hadj.2 (Set.mem_singleton_iff.mpr rfl)
    · simp only [if_pos hx, dif_neg hy]
      exact Fin.ext_iff.not.mpr (by simp)
    · simp only [if_neg hx, dif_pos hy]
      exact (by decide : (3 : Fin 4) ≠ 0)
    · simp only [if_neg hx, dif_neg hy]
      have := (c₂ ⟨y, Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm)⟩).isLt
      exact Fin.ext_iff.not.mpr (by simp; omega)
  · simp [deleteEdges_adj, toft5] at hadj
  · rw [deleteEdges_adj] at hadj
    by_cases hx : x = w <;> by_cases hy : y = u
    · subst hx hy; exfalso; exact hadj.2 (Set.mem_singleton_iff.mpr Sym2.eq_swap)
    · simp only [dif_pos hx, if_neg hy]
      exact (by decide : (0 : Fin 4) ≠ 3)
    · simp only [dif_neg hx, if_pos hy]
      exact Fin.ext_iff.not.mpr (by simp)
    · simp only [dif_neg hx, if_neg hy]
      have := (c₂ ⟨x, Set.mem_univ x, fun hm => hx (Set.mem_singleton_iff.mp hm)⟩).isLt
      exact Fin.ext_iff.not.mpr (by simp; omega)
  · rw [deleteEdges_adj] at hadj
    by_cases hx : x = w <;> by_cases hy : y = w
    · subst hx hy; exact absurd rfl (G₂.ne_of_adj hadj.1)
    · simp only [dif_pos hx, dif_neg hy]
      exact Fin.ext_iff.not.mpr (by simp)
    · simp only [dif_neg hx, dif_pos hy]
      exact Fin.ext_iff.not.mpr (by simp)
    · simp only [dif_neg hx, dif_neg hy]
      have hadj2 : ((⊤ : G₂.Subgraph).deleteVerts {w}).coe.Adj
          ⟨x, Set.mem_univ x, fun hm => hx (Set.mem_singleton_iff.mp hm)⟩
          ⟨y, Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm)⟩ := by
        rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
        exact ⟨Set.mem_univ x, fun hm => hx (Set.mem_singleton_iff.mp hm),
          Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm),
          Subgraph.top_adj.mpr hadj.1⟩
      exact ((Fin.castSucc_injective 3).comp (Fin.succ_injective 2)).ne (c₂.valid hadj2)

lemma toft5_isKCritical {n₁ n₂ : ℕ}
    {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    (h₁ : Erdos917.IsKCritical G₁ 4) (h₂ : Erdos917.IsKCritical G₂ 3) :
    Erdos917.IsKCritical (toft5 G₁ G₂) 5 := by
  have hn₁ : 0 < n₁ := Nat.pos_of_ne_zero fun h0 => by
    subst h0; have := h₁.1.1; simp [chromaticNumber_eq_zero_of_isEmpty] at this
  have hcol₁ : G₁.Colorable 4 := colorable_of_chromaticNumber_eq h₁.1.1
  have hcol₂ : G₂.Colorable 3 := colorable_of_chromaticNumber_eq h₂.1.1
  have hchi : (toft5 G₁ G₂).chromaticNumber = (5 : ℕ∞) := by
    have h := (chromaticNumber_eq_iff_colorable_not_colorable (G := toft5 G₁ G₂) (n := 4)).mpr
      ⟨toft5_colorable5 hcol₁ hcol₂, toft5_not_colorable4 hn₁ h₁.1.1 h₂.1.1⟩
    rw [h]
    norm_num
  apply isKCritical_of_edgeCritical_of_no_isolated hchi
  · intro e he
    induction e using Sym2.ind with | _ a b =>
    change ((toft5 G₁ G₂).deleteEdges {s(a, b)}).chromaticNumber < (toft5 G₁ G₂).chromaticNumber
    rw [hchi]
    have hlt : (4 : ℕ∞) < (5 : ℕ∞) := by norm_num
    refine lt_of_le_of_lt (Colorable.chromaticNumber_le ?_) hlt
    rcases a with (u | u) | u <;> rcases b with (v | v) | v
    · exact toft5_delete_A (colorable_deleteEdge (by norm_num) h₁.1.1 (h₁.2 s(u, v) he)) hcol₂
    · have huv : u = v := he; subst huv
      exact toft5_delete_match (colorable_deleteVert (by norm_num) h₁.1 u) hcol₂
    · simp [toft5] at he
    · have huv : u = v := he; subst huv; rw [Sym2.eq_swap]
      exact toft5_delete_match (colorable_deleteVert (by norm_num) h₁.1 u) hcol₂
    · simp [toft5] at he
    · exact toft5_delete_cross (colorable_deleteVert (by norm_num) h₁.1 u)
        (colorable_deleteVert (by norm_num) h₂.1 v)
    · simp [toft5] at he
    · rw [Sym2.eq_swap]
      exact toft5_delete_cross (colorable_deleteVert (by norm_num) h₁.1 v)
        (colorable_deleteVert (by norm_num) h₂.1 u)
    · exact toft5_delete_C hcol₁ (colorable_deleteEdge (by norm_num) h₂.1.1 (h₂.2 s(u, v) he))
  · rintro ((u | u) | w)
    · exact ⟨Sum.inl (Sum.inr u), rfl⟩
    · exact ⟨Sum.inl (Sum.inl u), rfl⟩
    · exact ⟨Sum.inl (Sum.inr ⟨0, hn₁⟩), trivial⟩

lemma sym2_map_inj {α β : Type*} {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Sym2.map f) := by
  intro e₁ e₂ h
  induction e₁ using Sym2.ind with | _ a₁ b₁ =>
  induction e₂ using Sym2.ind with | _ a₂ b₂ =>
  simp only [Sym2.map_mk, Sym2.eq_iff] at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hf h1, hf h2⟩
  · exact Or.inr ⟨hf h1, hf h2⟩

lemma toft5_edgeSet_ncard {n₁ n₂ : ℕ}
    (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂)) :
    (toft5 G₁ G₂).edgeSet.ncard = G₁.edgeSet.ncard + G₂.edgeSet.ncard + n₁ + n₁ * n₂ := by
  let f₁ : Fin n₁ → V n₁ n₂ := fun u => Sum.inl (Sum.inl u)
  let f₂ : Fin n₂ → V n₁ n₂ := fun w => Sum.inr w
  have hf₁ : Function.Injective f₁ := Sum.inl_injective.comp Sum.inl_injective
  have hf₂ : Function.Injective f₂ := Sum.inr_injective
  let E₁ : Set (Sym2 (V n₁ n₂)) := Sym2.map f₁ '' G₁.edgeSet
  let E₂ : Set (Sym2 (V n₁ n₂)) := Sym2.map f₂ '' G₂.edgeSet
  let M : Set (Sym2 (V n₁ n₂)) := (fun u : Fin n₁ => (s(Sum.inl (Sum.inl u), Sum.inl (Sum.inr u)) : Sym2 (V n₁ n₂))) '' Set.univ
  let C : Set (Sym2 (V n₁ n₂)) := (fun p : Fin n₁ × Fin n₂ => (s(Sum.inl (Sum.inr p.1), Sum.inr p.2) : Sym2 (V n₁ n₂))) '' Set.univ
  have hunion : (toft5 G₁ G₂).edgeSet = E₁ ∪ (E₂ ∪ (M ∪ C)) := by
    ext e
    constructor
    · intro he
      induction e using Sym2.ind with | _ a b =>
      rcases a with (u | u) | u <;> rcases b with (v | v) | v
      · exact Or.inl ⟨s(u, v), he, rfl⟩
      · have huv : u = v := he; subst huv; exact Or.inr (Or.inr (Or.inl ⟨u, trivial, rfl⟩))
      · simp [toft5] at he
      · have huv : u = v := he; subst huv; exact Or.inr (Or.inr (Or.inl ⟨u, trivial, Sym2.eq_swap⟩))
      · simp [toft5] at he
      · exact Or.inr (Or.inr (Or.inr ⟨(u, v), trivial, rfl⟩))
      · simp [toft5] at he
      · exact Or.inr (Or.inr (Or.inr ⟨(v, u), trivial, Sym2.eq_swap⟩))
      · exact Or.inr (Or.inl ⟨s(u, v), he, rfl⟩)
    · rintro (⟨e₁, he₁, rfl⟩ | ⟨e₂, he₂, rfl⟩ | ⟨u, -, rfl⟩ | ⟨⟨u, w⟩, -, rfl⟩)
      · induction e₁ using Sym2.ind with | _ u v => exact he₁
      · induction e₂ using Sym2.ind with | _ u v => exact he₂
      · exact rfl
      · trivial
  have hE₁ : E₁.ncard = G₁.edgeSet.ncard := Set.ncard_image_of_injective _ (sym2_map_inj hf₁)
  have hE₂ : E₂.ncard = G₂.edgeSet.ncard := Set.ncard_image_of_injective _ (sym2_map_inj hf₂)
  have hMinj : Function.Injective (fun u : Fin n₁ => (s(Sum.inl (Sum.inl u), Sum.inl (Sum.inr u)) : Sym2 (V n₁ n₂))) := by
    intro u v h; simp only [Sym2.eq_iff] at h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> simp_all
  have hCinj : Function.Injective (fun p : Fin n₁ × Fin n₂ => (s(Sum.inl (Sum.inr p.1), Sum.inr p.2) : Sym2 (V n₁ n₂))) := by
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ h; simp only [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, _⟩
    · simp only [Sum.inl.injEq, Sum.inr.injEq] at h1 h2; exact Prod.ext h1 h2
    · simp at h1
  have hM : M.ncard = n₁ := by
    rw [Set.ncard_image_of_injective _ hMinj, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hC : C.ncard = n₁ * n₂ := by
    rw [Set.ncard_image_of_injective _ hCinj, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have dE₁ : Disjoint E₁ (E₂ ∪ (M ∪ C)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨e₁, -, rfl⟩ h
    induction e₁ using Sym2.ind with | _ u v =>
    rcases h with ⟨e₂, -, heq⟩ | ⟨w, -, heq⟩ | ⟨⟨a, b⟩, -, heq⟩
    · induction e₂ using Sym2.ind with | _ a b => simp [f₁, f₂] at heq
    · simp [f₁] at heq
    · simp [f₁] at heq
  have dE₂ : Disjoint E₂ (M ∪ C) := by
    rw [Set.disjoint_left]
    rintro _ ⟨e₂, -, rfl⟩ h
    induction e₂ using Sym2.ind with | _ u v =>
    rcases h with ⟨w, -, heq⟩ | ⟨⟨a, b⟩, -, heq⟩ <;> simp [f₂] at heq
  have dMC : Disjoint M C := by
    rw [Set.disjoint_left]
    rintro _ ⟨u, -, rfl⟩ ⟨⟨a, b⟩, -, heq⟩
    simp at heq
  rw [hunion, Set.ncard_union_eq dE₁, Set.ncard_union_eq dE₂,
    Set.ncard_union_eq dMC, hE₁, hE₂, hM, hC]
  omega

lemma topSubgraph_lt_of_colorable {W : Type*} {G : SimpleGraph W} {k : ℕ}
    (hchi : G.chromaticNumber = (k : ℕ∞)) {v : W}
    (hcol : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable (k - 1)) (_hk : 1 ≤ k) :
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

lemma iso_isKCritical {W₁ W₂ : Type*} {G : SimpleGraph W₁} {H : SimpleGraph W₂}
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

lemma iso_edgeSet_ncard {W₁ W₂ : Type*} {G : SimpleGraph W₁} {H : SimpleGraph W₂}
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

end OMA.Toft5

theorem OMA.solution : OMA.R_Erdos917_erdos_917_variants_lower_construction_R1.H4 := by
  intro n₁ n₂ e₁ e₂ ⟨G₁, hG₁, he₁⟩ ⟨G₂, hG₂, he₂⟩
  let J := OMA.Toft5.toft5 G₁ G₂
  let equiv : OMA.Toft5.V n₁ n₂ ≃ Fin (2 * n₁ + n₂) :=
    Fintype.equivFinOfCardEq (by simp [OMA.Toft5.V]; omega)
  let G : SimpleGraph (Fin (2 * n₁ + n₂)) := J.comap equiv.symm
  let iso : J ≃g G :=
    { toEquiv := equiv
      map_rel_iff' := by
        intro a b
        change J.Adj (equiv.symm (equiv a)) (equiv.symm (equiv b)) ↔ J.Adj a b
        simp }
  refine ⟨G, OMA.Toft5.iso_isKCritical iso (by norm_num)
    (OMA.Toft5.toft5_isKCritical hG₁ hG₂), ?_⟩
  rw [OMA.Toft5.iso_edgeSet_ncard iso, OMA.Toft5.toft5_edgeSet_ncard, he₁, he₂]
