import OMAReductions.R_Erdos917_erdos_917_variants_lower_construction_R1

/-!
# Proof of `Erdos917.erdos_917.variants.lower_construction.R1.H3` (Toft's 4-critical graph)

Given two `3`-critical graphs `G₁` on `n₁` vertices and `G₂` on `n₂` vertices, Toft's graph
`D(G₁, G₂)` takes `G₁` on `A₁`, `G₂` on `A₂`, independent copies `B₁, B₂` matched to `A₁, A₂`,
and all cross-edges between `B₁` and `B₂`. It is `4`-critical and has `e₁ + e₂ + n₁ + n₂ + n₁ * n₂`
edges.
-/

open SimpleGraph

namespace OMA.Toft4

/-- Vertex set `A₁ ⊔ B₁ ⊔ A₂ ⊔ B₂` of Toft's `4`-critical construction. -/
abbrev V (n₁ n₂ : ℕ) := (Fin n₁ ⊕ Fin n₁) ⊕ (Fin n₂ ⊕ Fin n₂)

/-- Toft's graph `D(G₁, G₂)` on `(Fin n₁ ⊕ Fin n₁) ⊕ (Fin n₂ ⊕ Fin n₂)`. -/
def toft4 {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂)) :
    SimpleGraph (V n₁ n₂) where
  Adj
    | Sum.inl (Sum.inl u), Sum.inl (Sum.inl v) => G₁.Adj u v
    | Sum.inl (Sum.inl u), Sum.inl (Sum.inr v) => u = v
    | Sum.inl (Sum.inr u), Sum.inl (Sum.inl v) => u = v
    | Sum.inl (Sum.inr _), Sum.inr (Sum.inr _) => True
    | Sum.inr (Sum.inr _), Sum.inl (Sum.inr _) => True
    | Sum.inr (Sum.inl u), Sum.inr (Sum.inl v) => G₂.Adj u v
    | Sum.inr (Sum.inl u), Sum.inr (Sum.inr v) => u = v
    | Sum.inr (Sum.inr u), Sum.inr (Sum.inl v) => u = v
    | _, _ => False
  symm := ⟨by
    rintro ((u | u) | (u | u)) ((v | v) | (v | v)) h <;>
      first | exact h | exact h.symm⟩
  loopless := ⟨by
    rintro ((u | u) | (u | u)) h <;>
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

lemma toft4_colorable4 {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    (h₁ : G₁.Colorable 3) (h₂ : G₂.Coloring (Fin 3)) :
    (toft4 G₁ G₂).Colorable 4 := by
  obtain ⟨c₁⟩ := h₁
  refine ⟨Coloring.mk (fun x => match x with
    | Sum.inl (Sum.inl u) => (c₁ u).castSucc
    | Sum.inl (Sum.inr _) => 3
    | Sum.inr (Sum.inl w) => (h₂ w).succ
    | Sum.inr (Sum.inr _) => 0) ?_⟩
  rintro ((u | u) | (u | u)) ((v | v) | (v | v)) hadj
  · exact Fin.castSucc_injective 3 |>.ne (c₁.valid hadj)
  · exact Fin.castSucc_lt_last (c₁ u) |>.ne
  · simp [toft4] at hadj
  · simp [toft4] at hadj
  · exact (Fin.castSucc_lt_last (c₁ v)).ne.symm
  · simp [toft4] at hadj
  · simp [toft4] at hadj
  · exact (by decide : (3 : Fin 4) ≠ 0)
  · simp [toft4] at hadj
  · simp [toft4] at hadj
  · exact Fin.succ_injective 3 |>.ne (h₂.valid hadj)
  · exact (Fin.succ_pos (h₂ u)).ne'
  · simp [toft4] at hadj
  · exact (by decide : (0 : Fin 4) ≠ 3)
  · exact (Fin.succ_pos (h₂ v)).ne
  · simp [toft4] at hadj

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

lemma toft4_not_colorable3 {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hchi₁ : G₁.chromaticNumber = (3 : ℕ∞)) (hchi₂ : G₂.chromaticNumber = (3 : ℕ∞)) :
    ¬ (toft4 G₁ G₂).Colorable 3 := by
  rintro ⟨c⟩
  let S₁ : Finset (Fin 3) := Finset.univ.image (fun i : Fin n₁ => c (Sum.inl (Sum.inr i)))
  let S₂ : Finset (Fin 3) := Finset.univ.image (fun j : Fin n₂ => c (Sum.inr (Sum.inr j)))
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx2
    exact (c.valid (show (toft4 G₁ G₂).Adj (Sum.inl (Sum.inr i)) (Sum.inr (Sum.inr j)) from trivial)) hj.symm
  have hne₁ : 0 < S₁.card := Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, hn₁⟩)⟩
  have hne₂ : 0 < S₂.card := Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, hn₂⟩)⟩
  have hsum : S₁.card + S₂.card ≤ 3 := by
    have h1 : S₁.card + S₂.card = (S₁ ∪ S₂).card := (Finset.card_union_of_disjoint hdisj).symm
    have h2 : (S₁ ∪ S₂).card ≤ 3 := by simpa using Finset.card_le_univ (S₁ ∪ S₂)
    omega
  have hcase : S₁.card = 1 ∨ S₂.card = 1 := by omega
  rcases hcase with h1 | h2
  · obtain ⟨col, hcol⟩ := Finset.card_eq_one.mp h1
    have hB₁ : ∀ i : Fin n₁, c (Sum.inl (Sum.inr i)) = col := fun i =>
      Finset.mem_singleton.mp (hcol ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hA₁ : ∀ i : Fin n₁, c (Sum.inl (Sum.inl i)) ≠ col := fun i => by
      rw [← hB₁ i]
      exact c.valid (show (toft4 G₁ G₂).Adj (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inr i)) from rfl)
    have hcol2 : G₁.Colorable 2 :=
      ⟨Coloring.mk (fun i =>
        ⟨if (c (Sum.inl (Sum.inl i))).val < col.val then (c (Sum.inl (Sum.inl i))).val
         else (c (Sum.inl (Sum.inl i))).val - 1, by
          have := (c (Sum.inl (Sum.inl i))).isLt; have := col.isLt; split_ifs <;> omega⟩)
        fun {i i'} hii => drop_color col _ _ (hA₁ i) (hA₁ i') (c.valid hii)⟩
    have hle : (3 : ℕ∞) ≤ (2 : ℕ∞) := hchi₁ ▸ hcol2.chromaticNumber_le
    norm_num at hle
  · obtain ⟨col, hcol⟩ := Finset.card_eq_one.mp h2
    have hB₂ : ∀ j : Fin n₂, c (Sum.inr (Sum.inr j)) = col := fun j =>
      Finset.mem_singleton.mp (hcol ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j))
    have hA₂ : ∀ j : Fin n₂, c (Sum.inr (Sum.inl j)) ≠ col := fun j => by
      rw [← hB₂ j]
      exact c.valid (show (toft4 G₁ G₂).Adj (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inr j)) from rfl)
    have hcol2 : G₂.Colorable 2 :=
      ⟨Coloring.mk (fun j =>
        ⟨if (c (Sum.inr (Sum.inl j))).val < col.val then (c (Sum.inr (Sum.inl j))).val
         else (c (Sum.inr (Sum.inl j))).val - 1, by
          have := (c (Sum.inr (Sum.inl j))).isLt; have := col.isLt; split_ifs <;> omega⟩)
        fun {j j'} hjj => drop_color col _ _ (hA₂ j) (hA₂ j') (c.valid hjj)⟩
    have hle : (3 : ℕ∞) ≤ (2 : ℕ∞) := hchi₂ ▸ hcol2.chromaticNumber_le
    norm_num at hle

lemma ne_flip3 (a : Fin 3) : a ≠ if a = 0 then 1 else 0 := by
  fin_cases a <;> decide

lemma toft4_delete_A1 {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    {u v : Fin n₁} (h₁ : (G₁.deleteEdges {s(u, v)}).Colorable 2) (h₂ : G₂.Colorable 3) :
    ((toft4 G₁ G₂).deleteEdges {s(Sum.inl (Sum.inl u), Sum.inl (Sum.inl v))}).Colorable 3 := by
  obtain ⟨c₁⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  refine ⟨Coloring.mk (fun x => match x with
    | Sum.inl (Sum.inl y) => (c₁ y).castSucc
    | Sum.inl (Sum.inr _) => 2
    | Sum.inr (Sum.inl z) => c₂ z
    | Sum.inr (Sum.inr z) => if c₂ z = 0 then 1 else 0) ?_⟩
  rintro ((x | x) | (x | x)) ((y | y) | (y | y)) hadj
  · rw [deleteEdges_adj] at hadj
    have hne : s(x, y) ∉ ({s(u, v)} : Set (Sym2 (Fin n₁))) := by
      intro hmem
      apply hadj.2
      rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem ⊢
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    exact (Fin.castSucc_injective 2).ne (c₁.valid (deleteEdges_adj.mpr ⟨hadj.1, hne⟩))
  · exact (Fin.castSucc_lt_last (c₁ x)).ne
  · simp [deleteEdges_adj, toft4] at hadj
  · simp [deleteEdges_adj, toft4] at hadj
  · exact (Fin.castSucc_lt_last (c₁ y)).ne.symm
  · simp [deleteEdges_adj, toft4] at hadj
  · simp [deleteEdges_adj, toft4] at hadj
  · change (2 : Fin 3) ≠ if c₂ y = 0 then 1 else 0
    split_ifs <;> decide
  · simp [deleteEdges_adj, toft4] at hadj
  · simp [deleteEdges_adj, toft4] at hadj
  · rw [deleteEdges_adj] at hadj
    exact c₂.valid hadj.1
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    exact ne_flip3 (c₂ x)
  · simp [deleteEdges_adj, toft4] at hadj
  · change (if c₂ x = 0 then (1 : Fin 3) else 0) ≠ 2
    split_ifs <;> decide
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    exact (ne_flip3 (c₂ x)).symm
  · simp [deleteEdges_adj, toft4] at hadj

lemma toft4_delete_A2 {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    {u v : Fin n₂} (h₁ : G₁.Colorable 3) (h₂ : (G₂.deleteEdges {s(u, v)}).Colorable 2) :
    ((toft4 G₁ G₂).deleteEdges {s(Sum.inr (Sum.inl u), Sum.inr (Sum.inl v))}).Colorable 3 := by
  obtain ⟨c₁⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  refine ⟨Coloring.mk (fun x => match x with
    | Sum.inl (Sum.inl z) => c₁ z
    | Sum.inl (Sum.inr z) => if c₁ z = 0 then 1 else 0
    | Sum.inr (Sum.inl y) => (c₂ y).castSucc
    | Sum.inr (Sum.inr _) => 2) ?_⟩
  rintro ((x | x) | (x | x)) ((y | y) | (y | y)) hadj
  · rw [deleteEdges_adj] at hadj
    exact c₁.valid hadj.1
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    exact ne_flip3 (c₁ x)
  · simp [deleteEdges_adj, toft4] at hadj
  · simp [deleteEdges_adj, toft4] at hadj
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    exact (ne_flip3 (c₁ x)).symm
  · simp [deleteEdges_adj, toft4] at hadj
  · simp [deleteEdges_adj, toft4] at hadj
  · change (if c₁ x = 0 then (1 : Fin 3) else 0) ≠ 2
    split_ifs <;> decide
  · simp [deleteEdges_adj, toft4] at hadj
  · simp [deleteEdges_adj, toft4] at hadj
  · rw [deleteEdges_adj] at hadj
    have hne : s(x, y) ∉ ({s(u, v)} : Set (Sym2 (Fin n₂))) := by
      intro hmem
      apply hadj.2
      rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem ⊢
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    exact (Fin.castSucc_injective 2).ne (c₂.valid (deleteEdges_adj.mpr ⟨hadj.1, hne⟩))
  · exact (Fin.castSucc_lt_last (c₂ x)).ne
  · simp [deleteEdges_adj, toft4] at hadj
  · change (2 : Fin 3) ≠ if c₁ y = 0 then 1 else 0
    split_ifs <;> decide
  · exact (Fin.castSucc_lt_last (c₂ y)).ne.symm
  · simp [deleteEdges_adj, toft4] at hadj

lemma toft4_delete_match1 {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    {u : Fin n₁}
    (h₁ : ((⊤ : G₁.Subgraph).deleteVerts {u}).coe.Colorable 2) (h₂ : G₂.Colorable 3) :
    ((toft4 G₁ G₂).deleteEdges {s(Sum.inl (Sum.inl u), Sum.inl (Sum.inr u))}).Colorable 3 := by
  obtain ⟨c₁⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  refine ⟨Coloring.mk (fun x => match x with
    | Sum.inl (Sum.inl y) =>
      if hy : y = u then 2
      else (c₁ ⟨y, Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm)⟩).castSucc
    | Sum.inl (Sum.inr _) => 2
    | Sum.inr (Sum.inl z) => c₂ z
    | Sum.inr (Sum.inr z) => if c₂ z = 0 then 1 else 0) ?_⟩
  rintro ((x | x) | (x | x)) ((y | y) | (y | y)) hadj
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
      exact (Fin.castSucc_injective 2).ne (c₁.valid hadj1)
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    by_cases hx : x = u
    · subst hx; exfalso; exact hadj.2 (Set.mem_singleton_iff.mpr rfl)
    · simp only [dif_neg hx]
      exact (Fin.castSucc_lt_last _).ne
  · simp [deleteEdges_adj, toft4] at hadj
  · simp [deleteEdges_adj, toft4] at hadj
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    by_cases hx : x = u
    · subst hx; exfalso; exact hadj.2 (Set.mem_singleton_iff.mpr Sym2.eq_swap)
    · simp only [dif_neg hx]
      exact (Fin.castSucc_lt_last _).ne.symm
  · simp [deleteEdges_adj, toft4] at hadj
  · simp [deleteEdges_adj, toft4] at hadj
  · change (2 : Fin 3) ≠ if c₂ y = 0 then 1 else 0
    split_ifs <;> decide
  · simp [deleteEdges_adj, toft4] at hadj
  · simp [deleteEdges_adj, toft4] at hadj
  · rw [deleteEdges_adj] at hadj
    exact c₂.valid hadj.1
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    exact ne_flip3 (c₂ x)
  · simp [deleteEdges_adj, toft4] at hadj
  · change (if c₂ x = 0 then (1 : Fin 3) else 0) ≠ 2
    split_ifs <;> decide
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    exact (ne_flip3 (c₂ x)).symm
  · simp [deleteEdges_adj, toft4] at hadj

lemma toft4_delete_match2 {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    {w : Fin n₂}
    (h₁ : G₁.Colorable 3) (h₂ : ((⊤ : G₂.Subgraph).deleteVerts {w}).coe.Colorable 2) :
    ((toft4 G₁ G₂).deleteEdges {s(Sum.inr (Sum.inl w), Sum.inr (Sum.inr w))}).Colorable 3 := by
  obtain ⟨c₁⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  refine ⟨Coloring.mk (fun x => match x with
    | Sum.inl (Sum.inl z) => c₁ z
    | Sum.inl (Sum.inr z) => if c₁ z = 0 then 1 else 0
    | Sum.inr (Sum.inl y) =>
      if hy : y = w then 2
      else (c₂ ⟨y, Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm)⟩).castSucc
    | Sum.inr (Sum.inr _) => 2) ?_⟩
  rintro ((x | x) | (x | x)) ((y | y) | (y | y)) hadj
  · rw [deleteEdges_adj] at hadj
    exact c₁.valid hadj.1
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    exact ne_flip3 (c₁ x)
  · simp [deleteEdges_adj, toft4] at hadj
  · simp [deleteEdges_adj, toft4] at hadj
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    exact (ne_flip3 (c₁ x)).symm
  · simp [deleteEdges_adj, toft4] at hadj
  · simp [deleteEdges_adj, toft4] at hadj
  · change (if c₁ x = 0 then (1 : Fin 3) else 0) ≠ 2
    split_ifs <;> decide
  · simp [deleteEdges_adj, toft4] at hadj
  · simp [deleteEdges_adj, toft4] at hadj
  · rw [deleteEdges_adj] at hadj
    by_cases hx : x = w <;> by_cases hy : y = w
    · subst hx hy; exact absurd rfl (G₂.ne_of_adj hadj.1)
    · simp only [dif_pos hx, dif_neg hy]
      exact (Fin.castSucc_lt_last _).ne.symm
    · simp only [dif_neg hx, dif_pos hy]
      exact (Fin.castSucc_lt_last _).ne
    · simp only [dif_neg hx, dif_neg hy]
      have hadj2 : ((⊤ : G₂.Subgraph).deleteVerts {w}).coe.Adj
          ⟨x, Set.mem_univ x, fun hm => hx (Set.mem_singleton_iff.mp hm)⟩
          ⟨y, Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm)⟩ := by
        rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
        exact ⟨Set.mem_univ x, fun hm => hx (Set.mem_singleton_iff.mp hm),
          Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm),
          Subgraph.top_adj.mpr hadj.1⟩
      exact (Fin.castSucc_injective 2).ne (c₂.valid hadj2)
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    by_cases hx : x = w
    · subst hx; exfalso; exact hadj.2 (Set.mem_singleton_iff.mpr rfl)
    · simp only [dif_neg hx]
      exact (Fin.castSucc_lt_last _).ne
  · simp [deleteEdges_adj, toft4] at hadj
  · change (2 : Fin 3) ≠ if c₁ y = 0 then 1 else 0
    split_ifs <;> decide
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    by_cases hx : x = w
    · subst hx; exfalso; exact hadj.2 (Set.mem_singleton_iff.mpr Sym2.eq_swap)
    · simp only [dif_neg hx]
      exact (Fin.castSucc_lt_last _).ne.symm
  · simp [deleteEdges_adj, toft4] at hadj

lemma fin2_map_inj (a b : Fin 2) (h : a ≠ b) :
    (if a = 0 then (0 : Fin 3) else 2) ≠ (if b = 0 then (0 : Fin 3) else 2) := by
  fin_cases a <;> fin_cases b <;> simp_all

lemma toft4_delete_cross {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    {u : Fin n₁} {w : Fin n₂}
    (h₁ : ((⊤ : G₁.Subgraph).deleteVerts {u}).coe.Colorable 2)
    (h₂ : ((⊤ : G₂.Subgraph).deleteVerts {w}).coe.Colorable 2) :
    ((toft4 G₁ G₂).deleteEdges {s(Sum.inl (Sum.inr u), Sum.inr (Sum.inr w))}).Colorable 3 := by
  obtain ⟨c₁⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  refine ⟨Coloring.mk (fun x => match x with
    | Sum.inl (Sum.inl y) =>
      if hy : y = u then 1
      else if c₁ ⟨y, Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm)⟩ = 0 then 0 else 2
    | Sum.inl (Sum.inr y) => if y = u then 0 else 1
    | Sum.inr (Sum.inl z) =>
      if hz : z = w then 2
      else (c₂ ⟨z, Set.mem_univ z, fun hm => hz (Set.mem_singleton_iff.mp hm)⟩).castSucc
    | Sum.inr (Sum.inr z) => if z = w then 0 else 2) ?_⟩
  rintro ((x | x) | (x | x)) ((y | y) | (y | y)) hadj
  · rw [deleteEdges_adj] at hadj
    by_cases hx : x = u <;> by_cases hy : y = u
    · subst hx hy; exact absurd rfl (G₁.ne_of_adj hadj.1)
    · simp only [dif_pos hx, dif_neg hy]
      split_ifs <;> decide
    · simp only [dif_neg hx, dif_pos hy]
      split_ifs <;> decide
    · simp only [dif_neg hx, dif_neg hy]
      have hadj1 : ((⊤ : G₁.Subgraph).deleteVerts {u}).coe.Adj
          ⟨x, Set.mem_univ x, fun hm => hx (Set.mem_singleton_iff.mp hm)⟩
          ⟨y, Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm)⟩ := by
        rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
        exact ⟨Set.mem_univ x, fun hm => hx (Set.mem_singleton_iff.mp hm),
          Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm),
          Subgraph.top_adj.mpr hadj.1⟩
      exact fin2_map_inj _ _ (c₁.valid hadj1)
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    by_cases hx : x = u
    · simp [hx]
    · simp only [dif_neg hx, if_neg hx]
      split_ifs <;> decide
  · simp [deleteEdges_adj, toft4] at hadj
  · simp [deleteEdges_adj, toft4] at hadj
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    by_cases hx : x = u
    · simp [hx]
    · simp only [dif_neg hx, if_neg hx]
      split_ifs <;> decide
  · simp [deleteEdges_adj, toft4] at hadj
  · simp [deleteEdges_adj, toft4] at hadj
  · rw [deleteEdges_adj] at hadj
    by_cases hx : x = u <;> by_cases hy : y = w
    · subst hx hy; exfalso; exact hadj.2 (Set.mem_singleton_iff.mpr rfl)
    · simp [hx, hy]
    · simp [hx, hy]
    · simp [hx, hy]
  · simp [deleteEdges_adj, toft4] at hadj
  · simp [deleteEdges_adj, toft4] at hadj
  · rw [deleteEdges_adj] at hadj
    by_cases hx : x = w <;> by_cases hy : y = w
    · subst hx hy; exact absurd rfl (G₂.ne_of_adj hadj.1)
    · simp only [dif_pos hx, dif_neg hy]
      exact (Fin.castSucc_lt_last _).ne.symm
    · simp only [dif_neg hx, dif_pos hy]
      exact (Fin.castSucc_lt_last _).ne
    · simp only [dif_neg hx, dif_neg hy]
      have hadj2 : ((⊤ : G₂.Subgraph).deleteVerts {w}).coe.Adj
          ⟨x, Set.mem_univ x, fun hm => hx (Set.mem_singleton_iff.mp hm)⟩
          ⟨y, Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm)⟩ := by
        rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
        exact ⟨Set.mem_univ x, fun hm => hx (Set.mem_singleton_iff.mp hm),
          Set.mem_univ y, fun hm => hy (Set.mem_singleton_iff.mp hm),
          Subgraph.top_adj.mpr hadj.1⟩
      exact (Fin.castSucc_injective 2).ne (c₂.valid hadj2)
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    by_cases hx : x = w
    · simp [hx]
    · simp only [dif_neg hx, if_neg hx]
      exact (Fin.castSucc_lt_last _).ne
  · simp [deleteEdges_adj, toft4] at hadj
  · rw [deleteEdges_adj] at hadj
    by_cases hx : x = w <;> by_cases hy : y = u
    · subst hx hy; exfalso; exact hadj.2 (Set.mem_singleton_iff.mpr Sym2.eq_swap)
    · simp [hx, hy]
    · simp [hx, hy]
    · simp [hx, hy]
  · rw [deleteEdges_adj] at hadj
    have hxy : x = y := hadj.1
    subst hxy
    by_cases hx : x = w
    · simp [hx]
    · simp only [dif_neg hx, if_neg hx]
      exact (Fin.castSucc_lt_last _).ne.symm
  · simp [deleteEdges_adj, toft4] at hadj

lemma toft4_isKCritical {n₁ n₂ : ℕ}
    {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    (h₁ : Erdos917.IsKCritical G₁ 3) (h₂ : Erdos917.IsKCritical G₂ 3) :
    Erdos917.IsKCritical (toft4 G₁ G₂) 4 := by
  have hn₁ : 0 < n₁ := Nat.pos_of_ne_zero fun h0 => by
    subst h0; have := h₁.1.1; simp [chromaticNumber_eq_zero_of_isEmpty] at this
  have hn₂ : 0 < n₂ := Nat.pos_of_ne_zero fun h0 => by
    subst h0; have := h₂.1.1; simp [chromaticNumber_eq_zero_of_isEmpty] at this
  have hcol₁ : G₁.Colorable 3 := colorable_of_chromaticNumber_eq h₁.1.1
  have hcol₂ : G₂.Colorable 3 := colorable_of_chromaticNumber_eq h₂.1.1
  obtain ⟨c₂⟩ := hcol₂
  have hchi : (toft4 G₁ G₂).chromaticNumber = (4 : ℕ∞) := by
    have h := (chromaticNumber_eq_iff_colorable_not_colorable (G := toft4 G₁ G₂) (n := 3)).mpr
      ⟨toft4_colorable4 hcol₁ c₂, toft4_not_colorable3 hn₁ hn₂ h₁.1.1 h₂.1.1⟩
    rw [h]
    norm_num
  apply isKCritical_of_edgeCritical_of_no_isolated hchi
  · intro e he
    induction e using Sym2.ind with | _ a b =>
    change ((toft4 G₁ G₂).deleteEdges {s(a, b)}).chromaticNumber < (toft4 G₁ G₂).chromaticNumber
    rw [hchi]
    have hlt : (3 : ℕ∞) < (4 : ℕ∞) := by norm_num
    refine lt_of_le_of_lt (Colorable.chromaticNumber_le ?_) hlt
    rcases a with (u | u) | (u | u) <;> rcases b with (v | v) | (v | v)
    · exact toft4_delete_A1 (colorable_deleteEdge (by norm_num) h₁.1.1 (h₁.2 s(u, v) he)) ⟨c₂⟩
    · have huv : u = v := he
      subst huv
      exact toft4_delete_match1 (colorable_deleteVert (by norm_num) h₁.1 u) ⟨c₂⟩
    · simp [toft4] at he
    · simp [toft4] at he
    · have huv : u = v := he
      subst huv
      rw [Sym2.eq_swap]
      exact toft4_delete_match1 (colorable_deleteVert (by norm_num) h₁.1 u) ⟨c₂⟩
    · simp [toft4] at he
    · simp [toft4] at he
    · exact toft4_delete_cross (colorable_deleteVert (by norm_num) h₁.1 u)
        (colorable_deleteVert (by norm_num) h₂.1 v)
    · simp [toft4] at he
    · simp [toft4] at he
    · exact toft4_delete_A2 (colorable_of_chromaticNumber_eq h₁.1.1)
        (colorable_deleteEdge (by norm_num) h₂.1.1 (h₂.2 s(u, v) he))
    · have huv : u = v := he
      subst huv
      exact toft4_delete_match2 (colorable_of_chromaticNumber_eq h₁.1.1)
        (colorable_deleteVert (by norm_num) h₂.1 u)
    · simp [toft4] at he
    · rw [Sym2.eq_swap]
      exact toft4_delete_cross (colorable_deleteVert (by norm_num) h₁.1 v)
        (colorable_deleteVert (by norm_num) h₂.1 u)
    · have huv : u = v := he
      subst huv
      rw [Sym2.eq_swap]
      exact toft4_delete_match2 (colorable_of_chromaticNumber_eq h₁.1.1)
        (colorable_deleteVert (by norm_num) h₂.1 u)
    · simp [toft4] at he
  · rintro ((u | u) | (w | w))
    · exact ⟨Sum.inl (Sum.inr u), rfl⟩
    · exact ⟨Sum.inl (Sum.inl u), rfl⟩
    · exact ⟨Sum.inr (Sum.inr w), rfl⟩
    · exact ⟨Sum.inr (Sum.inl w), rfl⟩

lemma sym2_map_inj {α β : Type*} {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Sym2.map f) := by
  intro e₁ e₂ h
  induction e₁ using Sym2.ind with | _ a₁ b₁ =>
  induction e₂ using Sym2.ind with | _ a₂ b₂ =>
  simp only [Sym2.map_mk, Sym2.eq_iff] at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hf h1, hf h2⟩
  · exact Or.inr ⟨hf h1, hf h2⟩

lemma toft4_edgeSet_ncard {n₁ n₂ : ℕ}
    (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂)) :
    (toft4 G₁ G₂).edgeSet.ncard = G₁.edgeSet.ncard + G₂.edgeSet.ncard + n₁ + n₂ + n₁ * n₂ := by
  let f₁ : Fin n₁ → V n₁ n₂ := fun u => Sum.inl (Sum.inl u)
  let f₂ : Fin n₂ → V n₁ n₂ := fun w => Sum.inr (Sum.inl w)
  have hf₁ : Function.Injective f₁ := Sum.inl_injective.comp Sum.inl_injective
  have hf₂ : Function.Injective f₂ := Sum.inr_injective.comp Sum.inl_injective
  let E₁ : Set (Sym2 (V n₁ n₂)) := Sym2.map f₁ '' G₁.edgeSet
  let E₂ : Set (Sym2 (V n₁ n₂)) := Sym2.map f₂ '' G₂.edgeSet
  let M₁ : Set (Sym2 (V n₁ n₂)) := (fun u : Fin n₁ => s(Sum.inl (Sum.inl u), Sum.inl (Sum.inr u))) '' Set.univ
  let M₂ : Set (Sym2 (V n₁ n₂)) := (fun w : Fin n₂ => s(Sum.inr (Sum.inl w), Sum.inr (Sum.inr w))) '' Set.univ
  let C : Set (Sym2 (V n₁ n₂)) := (fun p : Fin n₁ × Fin n₂ => s(Sum.inl (Sum.inr p.1), Sum.inr (Sum.inr p.2))) '' Set.univ
  have hunion : (toft4 G₁ G₂).edgeSet = E₁ ∪ (E₂ ∪ (M₁ ∪ (M₂ ∪ C))) := by
    ext e
    constructor
    · intro he
      induction e using Sym2.ind with | _ a b =>
      rcases a with (u | u) | (u | u) <;> rcases b with (v | v) | (v | v)
      · exact Or.inl ⟨s(u, v), he, rfl⟩
      · have huv : u = v := he; subst huv; exact Or.inr (Or.inr (Or.inl ⟨u, trivial, rfl⟩))
      · simp [toft4] at he
      · simp [toft4] at he
      · have huv : u = v := he; subst huv; exact Or.inr (Or.inr (Or.inl ⟨u, trivial, Sym2.eq_swap⟩))
      · simp [toft4] at he
      · simp [toft4] at he
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(u, v), trivial, rfl⟩)))
      · simp [toft4] at he
      · simp [toft4] at he
      · exact Or.inr (Or.inl ⟨s(u, v), he, rfl⟩)
      · have huv : u = v := he; subst huv; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨u, trivial, rfl⟩)))
      · simp [toft4] at he
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(v, u), trivial, Sym2.eq_swap⟩)))
      · have huv : u = v := he; subst huv; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨u, trivial, Sym2.eq_swap⟩)))
      · simp [toft4] at he
    · rintro (⟨e₁, he₁, rfl⟩ | ⟨e₂, he₂, rfl⟩ | ⟨u, -, rfl⟩ | ⟨w, -, rfl⟩ | ⟨⟨u, w⟩, -, rfl⟩)
      · induction e₁ using Sym2.ind with | _ u v => exact he₁
      · induction e₂ using Sym2.ind with | _ u v => exact he₂
      · exact rfl
      · exact rfl
      · trivial
  have hE₁ : E₁.ncard = G₁.edgeSet.ncard := Set.ncard_image_of_injective _ (sym2_map_inj hf₁)
  have hE₂ : E₂.ncard = G₂.edgeSet.ncard := Set.ncard_image_of_injective _ (sym2_map_inj hf₂)
  have hM₁inj : Function.Injective (fun u : Fin n₁ => (s(Sum.inl (Sum.inl u), Sum.inl (Sum.inr u)) : Sym2 (V n₁ n₂))) := by
    intro u v h; simp only [Sym2.eq_iff] at h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> simp_all
  have hM₂inj : Function.Injective (fun w : Fin n₂ => (s(Sum.inr (Sum.inl w), Sum.inr (Sum.inr w)) : Sym2 (V n₁ n₂))) := by
    intro u v h; simp only [Sym2.eq_iff] at h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> simp_all
  have hCinj : Function.Injective (fun p : Fin n₁ × Fin n₂ => (s(Sum.inl (Sum.inr p.1), Sum.inr (Sum.inr p.2)) : Sym2 (V n₁ n₂))) := by
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ h; simp only [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, _⟩
    · simp only [Sum.inl.injEq, Sum.inr.injEq] at h1 h2; exact Prod.ext h1 h2
    · simp at h1
  have hM₁ : M₁.ncard = n₁ := by
    rw [Set.ncard_image_of_injective _ hM₁inj, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hM₂ : M₂.ncard = n₂ := by
    rw [Set.ncard_image_of_injective _ hM₂inj, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hC : C.ncard = n₁ * n₂ := by
    rw [Set.ncard_image_of_injective _ hCinj, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have dE₁ : Disjoint E₁ (E₂ ∪ (M₁ ∪ (M₂ ∪ C))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨e₁, -, rfl⟩ h
    induction e₁ using Sym2.ind with | _ u v =>
    rcases h with ⟨e₂, -, heq⟩ | ⟨w, -, heq⟩ | ⟨w, -, heq⟩ | ⟨⟨a, b⟩, -, heq⟩
    · induction e₂ using Sym2.ind with | _ a b => simp [f₁, f₂] at heq
    · simp [f₁] at heq
    · simp [f₁] at heq
    · simp [f₁] at heq
  have dE₂ : Disjoint E₂ (M₁ ∪ (M₂ ∪ C)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨e₂, -, rfl⟩ h
    induction e₂ using Sym2.ind with | _ u v =>
    rcases h with ⟨w, -, heq⟩ | ⟨w, -, heq⟩ | ⟨⟨a, b⟩, -, heq⟩ <;> simp [f₂] at heq
  have dM₁ : Disjoint M₁ (M₂ ∪ C) := by
    rw [Set.disjoint_left]
    rintro _ ⟨u, -, rfl⟩ h
    rcases h with ⟨w, -, heq⟩ | ⟨⟨a, b⟩, -, heq⟩ <;> simp at heq
  have dM₂ : Disjoint M₂ C := by
    rw [Set.disjoint_left]
    rintro _ ⟨u, -, rfl⟩ ⟨⟨a, b⟩, -, heq⟩
    simp at heq
  rw [hunion, Set.ncard_union_eq dE₁, Set.ncard_union_eq dE₂,
    Set.ncard_union_eq dM₁, Set.ncard_union_eq dM₂, hE₁, hE₂, hM₁, hM₂, hC]
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

end OMA.Toft4

theorem OMA.solution : OMA.R_Erdos917_erdos_917_variants_lower_construction_R1.H3 := by
  intro n₁ n₂ e₁ e₂ ⟨G₁, hG₁, he₁⟩ ⟨G₂, hG₂, he₂⟩
  let J := OMA.Toft4.toft4 G₁ G₂
  let equiv : OMA.Toft4.V n₁ n₂ ≃ Fin (2 * n₁ + 2 * n₂) :=
    Fintype.equivFinOfCardEq (by simp [OMA.Toft4.V]; omega)
  let G : SimpleGraph (Fin (2 * n₁ + 2 * n₂)) := J.comap equiv.symm
  let iso : J ≃g G :=
    { toEquiv := equiv
      map_rel_iff' := by
        intro a b
        change J.Adj (equiv.symm (equiv a)) (equiv.symm (equiv b)) ↔ J.Adj a b
        simp }
  refine ⟨G, OMA.Toft4.iso_isKCritical iso (by norm_num)
    (OMA.Toft4.toft4_isKCritical hG₁ hG₂), ?_⟩
  rw [OMA.Toft4.iso_edgeSet_ncard iso, OMA.Toft4.toft4_edgeSet_ncard, he₁, he₂]
