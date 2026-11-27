import OMAReductions.R_Erdos917_erdos_917_variants_lower_construction_R1

-- Step Erdos917.erdos_917.variants.lower_construction.R1.H2: hypothesis H2 of reduction Erdos917.erdos_917.variants.lower_construction.R1
-- Credit: @ZenimXD
--
-- Dirac's join theorem. The join J of a k₁-critical G₁ and a k₂-critical G₂ (all edges between
-- the two sides added) is (k₁ + k₂)-critical with e₁ + e₂ + n₁ n₂ edges:
-- * J is (k₁ + k₂)-colourable (disjoint palettes), and not (k₁ + k₂ - 1)-colourable, since the two
--   sides of any colouring use disjoint colour sets of sizes ≥ k₁ and ≥ k₂;
-- * deleting an edge inside G₁ (or G₂) leaves a (k₁ - 1) + k₂ colouring; deleting a cross edge uv
--   leaves the colouring (k₁ - 1 colours on G₁ - u) + (k₂ - 1 colours on G₂ - v) + one shared
--   colour for u and v;
-- * every vertex has a neighbour on the other side, so edge-criticality gives vertex-criticality.
-- The general criticality criterion, its transport along an equivalence and the edge count under
-- an equivalence are taken from the merged proof proofs/Erdos917.erdos_917.parts.i.lean.

open SimpleGraph Finset

namespace OMAStepErdos917H2

lemma colorable_of {V : Type*} (H : SimpleGraph V) (K : ℕ) (col : V → ℕ)
    (hb : ∀ x, col x < K) (hp : ∀ x y, H.Adj x y → col x ≠ col y) : H.Colorable K :=
  ⟨Coloring.mk (fun x => ⟨col x, hb x⟩) (fun {x y} h heq => hp x y h (congrArg Fin.val heq))⟩

lemma isKCritical_of_edge_critical {V : Type*} (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k)
    (hcol : G.Colorable k) (hnot : ¬ G.Colorable (k - 1))
    (hdeg : ∀ v : V, ∃ w : V, G.Adj v w)
    (hedge : ∀ u w : V, G.Adj u w → (G.deleteEdges {s(u, w)}).Colorable (k - 1)) :
    Erdos917.IsKCritical G k := by
  have hle_chi : (k : ℕ∞) ≤ G.chromaticNumber := by
    rw [le_chromaticNumber_iff_not_colorable (by omega)]
    exact hnot
  have hchi : G.chromaticNumber = (k : ℕ∞) :=
    le_antisymm hcol.chromaticNumber_le hle_chi
  refine ⟨⟨hchi, ?_⟩, ?_⟩
  · intro v
    unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts
    obtain ⟨w, hvw⟩ := hdeg v
    obtain ⟨C⟩ := hedge v w hvw
    have hdel : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable (k - 1) := by
      refine ⟨Coloring.mk (fun a => C a.val) ?_⟩
      intro a b hab
      rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj] at hab
      obtain ⟨_, ha, _, hb, hab⟩ := hab
      rw [Subgraph.top_adj] at hab
      apply C.valid
      rw [deleteEdges_adj]
      refine ⟨hab, ?_⟩
      rw [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact ha (Set.mem_singleton_iff.mpr h1)
      · exact hb (Set.mem_singleton_iff.mpr h2)
    have htop_le : (k : ℕ∞) ≤ (⊤ : G.Subgraph).coe.chromaticNumber := by
      rw [le_chromaticNumber_iff_not_colorable (by omega)]
      rintro ⟨C'⟩
      exact hnot ⟨Coloring.mk (fun x => C' ⟨x, trivial⟩) (fun h => C'.valid (by simpa using h))⟩
    exact lt_of_le_of_lt hdel.chromaticNumber_le
      (lt_of_lt_of_le (by exact_mod_cast (by omega : k - 1 < k)) htop_le)
  · intro e he
    unfold IsCriticalEdge IsCriticalEdges
    revert he
    refine Sym2.ind (fun u w huw => ?_) e
    rw [mem_edgeSet] at huw
    exact lt_of_le_of_lt (hedge u w huw).chromaticNumber_le
      (lt_of_lt_of_le (by exact_mod_cast (by omega : k - 1 < k)) hle_chi)

lemma isKCritical_transport {V W : Type*} (G : SimpleGraph V) (e : V ≃ W) {k : ℕ} (hk : 1 ≤ k)
    (hcol : G.Colorable k) (hnot : ¬ G.Colorable (k - 1))
    (hdeg : ∀ v : V, ∃ w : V, G.Adj v w)
    (hedge : ∀ u w : V, G.Adj u w → (G.deleteEdges {s(u, w)}).Colorable (k - 1)) :
    Erdos917.IsKCritical (G.map e.toEmbedding) k := by
  refine isKCritical_of_edge_critical _ hk ?_ ?_ ?_ ?_
  · obtain ⟨C⟩ := hcol
    refine ⟨Coloring.mk (fun w => C (e.symm w)) ?_⟩
    intro x y hxy
    rw [map_adj] at hxy
    obtain ⟨u, v, huv, rfl, rfl⟩ := hxy
    simpa using C.valid huv
  · rintro ⟨C⟩
    exact hnot ⟨Coloring.mk (fun v => C (e v)) fun {u v} huv =>
      C.valid (by rw [map_adj]; exact ⟨u, v, huv, rfl, rfl⟩)⟩
  · intro w
    obtain ⟨u, hu⟩ := hdeg (e.symm w)
    refine ⟨e u, ?_⟩
    rw [map_adj]
    exact ⟨e.symm w, u, hu, e.apply_symm_apply w, rfl⟩
  · intro x y hxy
    rw [map_adj] at hxy
    obtain ⟨u, v, huv, rfl, rfl⟩ := hxy
    obtain ⟨C⟩ := hedge u v huv
    refine ⟨Coloring.mk (fun w => C (e.symm w)) ?_⟩
    intro a b hab
    rw [deleteEdges_adj, map_adj] at hab
    obtain ⟨⟨u', v', huv', rfl, rfl⟩, hne⟩ := hab
    simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
    apply C.valid
    rw [deleteEdges_adj]
    refine ⟨huv', ?_⟩
    intro heq
    apply hne
    rw [Set.mem_singleton_iff] at heq ⊢
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap

lemma ncard_edgeSet_map {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : V ≃ W)
    [DecidableRel (G.map e.toEmbedding).Adj] :
    (G.map e.toEmbedding).edgeSet.ncard = G.edgeSet.ncard := by
  rw [← coe_edgeFinset, ← coe_edgeFinset, Set.ncard_coe_finset, Set.ncard_coe_finset]
  have hdeg : ∀ v : V, (G.map e.toEmbedding).degree (e v) = G.degree v := by
    intro v
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      neighborFinset_eq_filter, neighborFinset_eq_filter]
    refine card_bij (fun w _ => e.symm w) ?_ ?_ ?_
    · intro w hw
      rw [mem_filter] at hw ⊢
      refine ⟨mem_univ _, ?_⟩
      have hwadj := hw.2
      rw [map_adj] at hwadj
      obtain ⟨a, b, hab, ha, hb⟩ := hwadj
      have h1 : a = v := e.injective ha
      have h2 : b = e.symm w := by
        apply e.injective
        simpa using hb
      rwa [← h1, ← h2]
    · intro w₁ _ w₂ _ h
      exact e.symm.injective h
    · intro u hu
      rw [mem_filter] at hu
      refine ⟨e u, ?_, e.symm_apply_apply u⟩
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rw [map_adj]
      exact ⟨v, u, hu.2, rfl, rfl⟩
  have hsum1 := sum_degrees_eq_twice_card_edges (G.map e.toEmbedding)
  have hsum2 := sum_degrees_eq_twice_card_edges G
  have hsum_eq : ∑ w : W, (G.map e.toEmbedding).degree w = ∑ v : V, G.degree v := by
    rw [← e.sum_comp]
    exact sum_congr rfl fun v _ => hdeg v
  omega

/-- The join of two graphs: both graphs, plus every edge between the two sides. -/
def join {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) where
  Adj x y := match x, y with
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inr a, Sum.inr b => H.Adj a b
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
  symm := ⟨by
    rintro (a | a) (b | b) h
    · exact G.adj_symm h
    · trivial
    · trivial
    · exact H.adj_symm h⟩
  loopless := ⟨by
    rintro (a | a) h
    · exact G.irrefl h
    · exact H.irrefl h⟩

section join

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

@[simp] lemma join_inl_inl (a b : V) : (join G H).Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b := Iff.rfl
@[simp] lemma join_inr_inr (a b : W) : (join G H).Adj (Sum.inr a) (Sum.inr b) ↔ H.Adj a b := Iff.rfl
@[simp] lemma join_inl_inr (a : V) (b : W) : (join G H).Adj (Sum.inl a) (Sum.inr b) ↔ True := Iff.rfl
@[simp] lemma join_inr_inl (a : W) (b : V) : (join G H).Adj (Sum.inr a) (Sum.inl b) ↔ True := Iff.rfl

end join

lemma le_sub_one_of_lt' (x : ℕ∞) (k : ℕ) (h : x < k) : x ≤ ((k - 1 : ℕ) : ℕ∞) := by
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt h)
  norm_cast at h ⊢
  omega

section crit

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma crit_colorable (hG : Erdos917.IsKCritical G k) : G.Colorable k :=
  chromaticNumber_le_iff_colorable.mp (le_of_eq hG.1.1)

lemma crit_not_colorable (hG : Erdos917.IsKCritical G k) (hk : 1 ≤ k) : ¬ G.Colorable (k - 1) := by
  intro h
  have h1 := h.chromaticNumber_le
  rw [hG.1.1] at h1
  have h2 : k ≤ k - 1 := by exact_mod_cast h1
  omega

lemma crit_edge (hG : Erdos917.IsKCritical G k) (u w : V) (huw : G.Adj u w) :
    (G.deleteEdges {s(u, w)}).Colorable (k - 1) := by
  have h := hG.2 s(u, w) (by simpa using huw)
  unfold IsCriticalEdge IsCriticalEdges at h
  rw [hG.1.1] at h
  exact chromaticNumber_le_iff_colorable.mp (le_sub_one_of_lt' _ _ h)

lemma crit_vertex (hG : Erdos917.IsKCritical G k) (v : V) :
    ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable (k - 1) := by
  have h := hG.1.2 v
  unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts at h
  have htop : (⊤ : G.Subgraph).coe.chromaticNumber ≤ k := by
    obtain ⟨C⟩ := crit_colorable hG
    exact Colorable.chromaticNumber_le
      ⟨Coloring.mk (fun x => C x.val) (fun {x y} hxy => C.valid (by simpa using hxy))⟩
  exact chromaticNumber_le_iff_colorable.mp (le_sub_one_of_lt' _ _ (lt_of_lt_of_le h htop))

lemma crit_nonempty (hG : Erdos917.IsKCritical G k) (hk : 2 ≤ k) : Nonempty V := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  exact crit_not_colorable hG (by omega)
    ⟨Coloring.mk (fun v => isEmptyElim v) (fun {v} _ => isEmptyElim v)⟩

end crit

section main

variable {V W : Type*} {G₁ : SimpleGraph V} {G₂ : SimpleGraph W} {k₁ k₂ : ℕ}

lemma join_colorable (h₁ : G₁.Colorable k₁) (h₂ : G₂.Colorable k₂) :
    (join G₁ G₂).Colorable (k₁ + k₂) := by
  obtain ⟨c₁⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  refine colorable_of _ _ (Sum.elim (fun a => ((c₁ a : Fin k₁) : ℕ)) (fun b => k₁ + ((c₂ b : Fin k₂) : ℕ)))
    ?_ ?_
  · rintro (a | b)
    · have := (c₁ a).isLt
      simp only [Sum.elim_inl]
      omega
    · have := (c₂ b).isLt
      simp only [Sum.elim_inr]
      omega
  · rintro (a | a) (b | b) h
    · simp only [Sum.elim_inl]
      intro heq
      exact c₁.valid h (Fin.ext heq)
    · have := (c₁ a).isLt
      simp only [Sum.elim_inl, Sum.elim_inr]
      omega
    · have := (c₁ b).isLt
      simp only [Sum.elim_inl, Sum.elim_inr]
      omega
    · simp only [Sum.elim_inr]
      intro heq
      exact c₂.valid h (Fin.ext (by omega))

lemma join_not_colorable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    (h₁ : ¬ G₁.Colorable (k₁ - 1)) (h₂ : ¬ G₂.Colorable (k₂ - 1)) :
    ¬ (join G₁ G₂).Colorable (k₁ + k₂ - 1) := by
  classical
  rintro ⟨C⟩
  set S₁ := (Finset.univ : Finset V).image (fun a => C (Sum.inl a)) with hS₁
  set S₂ := (Finset.univ : Finset W).image (fun b => C (Sum.inr b)) with hS₂
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hc1
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hc2
    exact C.valid (show (join G₁ G₂).Adj (Sum.inl a) (Sum.inr b) from trivial) hb.symm
  have hU : (S₁ ∪ S₂).card ≤ k₁ + k₂ - 1 := by
    simpa using Finset.card_le_univ (S₁ ∪ S₂)
  have hsum := Finset.card_union_add_card_inter S₁ S₂
  rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.card_empty, add_zero] at hsum
  have hA : k₁ ≤ S₁.card := by
    by_contra hlt
    push Not at hlt
    apply h₁
    have hc : G₁.Colorable S₁.card :=
      ⟨Coloring.mk (fun a => S₁.equivFin ⟨C (Sum.inl a), Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩)
        (fun {a b} hab heq => C.valid (show (join G₁ G₂).Adj (Sum.inl a) (Sum.inl b) from hab)
          (congrArg Subtype.val (S₁.equivFin.injective heq)))⟩
    exact hc.mono (by omega)
  have hB : k₂ ≤ S₂.card := by
    by_contra hlt
    push Not at hlt
    apply h₂
    have hc : G₂.Colorable S₂.card :=
      ⟨Coloring.mk (fun a => S₂.equivFin ⟨C (Sum.inr a), Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩)
        (fun {a b} hab heq => C.valid (show (join G₁ G₂).Adj (Sum.inr a) (Sum.inr b) from hab)
          (congrArg Subtype.val (S₂.equivFin.injective heq)))⟩
    exact hc.mono (by omega)
  omega

lemma join_deg [Nonempty V] [Nonempty W] : ∀ v : V ⊕ W, ∃ w, (join G₁ G₂).Adj v w := by
  rintro (a | b)
  · exact ⟨Sum.inr (Classical.arbitrary W), trivial⟩
  · exact ⟨Sum.inl (Classical.arbitrary V), trivial⟩

lemma sym2_inl_ne {a b x y : V} (h : s((Sum.inl x : V ⊕ W), Sum.inl y) ∉ ({s(Sum.inl a, Sum.inl b)} : Set (Sym2 (V ⊕ W)))) :
    s(x, y) ∉ ({s(a, b)} : Set (Sym2 V)) := by
  intro h'
  apply h
  rw [Set.mem_singleton_iff] at h' ⊢
  rcases Sym2.eq_iff.mp h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Sym2.eq_swap

lemma sym2_inr_ne {a b x y : W} (h : s((Sum.inr x : V ⊕ W), Sum.inr y) ∉ ({s(Sum.inr a, Sum.inr b)} : Set (Sym2 (V ⊕ W)))) :
    s(x, y) ∉ ({s(a, b)} : Set (Sym2 W)) := by
  intro h'
  apply h
  rw [Set.mem_singleton_iff] at h' ⊢
  rcases Sym2.eq_iff.mp h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Sym2.eq_swap

/-- Deleting an edge inside the first side. -/
lemma join_edge_inl (hk₁ : 1 ≤ k₁) (a b : V) (h₁ : (G₁.deleteEdges {s(a, b)}).Colorable (k₁ - 1))
    (h₂ : G₂.Colorable k₂) :
    ((join G₁ G₂).deleteEdges {s(Sum.inl a, Sum.inl b)}).Colorable (k₁ + k₂ - 1) := by
  obtain ⟨D⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  refine colorable_of _ _ (Sum.elim (fun x => ((D x : Fin (k₁ - 1)) : ℕ))
    (fun y => (k₁ - 1) + ((c₂ y : Fin k₂) : ℕ))) ?_ ?_
  · rintro (x | y)
    · have := (D x).isLt
      simp only [Sum.elim_inl]
      omega
    · have := (c₂ y).isLt
      simp only [Sum.elim_inr]
      omega
  · rintro (x | x) (y | y) h <;> rw [deleteEdges_adj] at h
    · simp only [Sum.elim_inl]
      intro heq
      exact D.valid (v := x) (w := y) (deleteEdges_adj.2 ⟨h.1, sym2_inl_ne h.2⟩) (Fin.ext heq)
    · have := (D x).isLt
      simp only [Sum.elim_inl, Sum.elim_inr]
      omega
    · have := (D y).isLt
      simp only [Sum.elim_inl, Sum.elim_inr]
      omega
    · simp only [Sum.elim_inr]
      intro heq
      exact c₂.valid h.1 (Fin.ext (by omega))

/-- Deleting an edge inside the second side. -/
lemma join_edge_inr (hk₂ : 1 ≤ k₂) (a b : W) (h₁ : G₁.Colorable k₁)
    (h₂ : (G₂.deleteEdges {s(a, b)}).Colorable (k₂ - 1)) :
    ((join G₁ G₂).deleteEdges {s(Sum.inr a, Sum.inr b)}).Colorable (k₁ + k₂ - 1) := by
  obtain ⟨c₁⟩ := h₁
  obtain ⟨D⟩ := h₂
  refine colorable_of _ _ (Sum.elim (fun x => ((c₁ x : Fin k₁) : ℕ))
    (fun y => k₁ + ((D y : Fin (k₂ - 1)) : ℕ))) ?_ ?_
  · rintro (x | y)
    · have := (c₁ x).isLt
      simp only [Sum.elim_inl]
      omega
    · have := (D y).isLt
      simp only [Sum.elim_inr]
      omega
  · rintro (x | x) (y | y) h <;> rw [deleteEdges_adj] at h
    · simp only [Sum.elim_inl]
      intro heq
      exact c₁.valid h.1 (Fin.ext heq)
    · have := (c₁ x).isLt
      simp only [Sum.elim_inl, Sum.elim_inr]
      omega
    · have := (c₁ y).isLt
      simp only [Sum.elim_inl, Sum.elim_inr]
      omega
    · simp only [Sum.elim_inr]
      intro heq
      exact D.valid (v := x) (w := y) (deleteEdges_adj.2 ⟨h.1, sym2_inr_ne h.2⟩) (Fin.ext (by omega))

lemma mem_del {X : Type*} {G : SimpleGraph X} {a x : X} (hx : x ≠ a) :
    x ∈ ((⊤ : G.Subgraph).deleteVerts {a}).verts := by
  simp [hx]

/-- Deleting a cross edge `inl a — inr b`. -/
lemma join_edge_cross (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (a : V) (b : W)
    (h₁ : ((⊤ : G₁.Subgraph).deleteVerts {a}).coe.Colorable (k₁ - 1))
    (h₂ : ((⊤ : G₂.Subgraph).deleteVerts {b}).coe.Colorable (k₂ - 1)) :
    ((join G₁ G₂).deleteEdges {s(Sum.inl a, Sum.inr b)}).Colorable (k₁ + k₂ - 1) := by
  classical
  obtain ⟨D₁⟩ := h₁
  obtain ⟨D₂⟩ := h₂
  let f₁ : V → ℕ := fun x => if hx : x = a then k₁ + k₂ - 2 else ((D₁ ⟨x, mem_del hx⟩ : Fin (k₁ - 1)) : ℕ)
  let f₂ : W → ℕ := fun y =>
    if hy : y = b then k₁ + k₂ - 2 else (k₁ - 1) + ((D₂ ⟨y, mem_del hy⟩ : Fin (k₂ - 1)) : ℕ)
  have hf₁a : f₁ a = k₁ + k₂ - 2 := by simp [f₁]
  have hf₂b : f₂ b = k₁ + k₂ - 2 := by simp [f₂]
  have hf₁ : ∀ x (hx : x ≠ a), f₁ x = ((D₁ ⟨x, mem_del hx⟩ : Fin (k₁ - 1)) : ℕ) := by
    intro x hx
    simp [f₁, hx]
  have hf₂ : ∀ y (hy : y ≠ b), f₂ y = (k₁ - 1) + ((D₂ ⟨y, mem_del hy⟩ : Fin (k₂ - 1)) : ℕ) := by
    intro y hy
    simp [f₂, hy]
  have hb₁ : ∀ x (hx : x ≠ a), f₁ x < k₁ - 1 := by
    intro x hx
    rw [hf₁ x hx]
    exact (D₁ _).isLt
  have hb₂ : ∀ y (hy : y ≠ b), k₁ - 1 ≤ f₂ y ∧ f₂ y < k₁ + k₂ - 2 := by
    intro y hy
    rw [hf₂ y hy]
    have := (D₂ ⟨y, mem_del hy⟩).isLt
    omega
  refine colorable_of _ _ (Sum.elim f₁ f₂) ?_ ?_
  · rintro (x | y)
    · simp only [Sum.elim_inl]
      by_cases hx : x = a
      · subst hx
        rw [hf₁a]
        omega
      · have := hb₁ x hx
        omega
    · simp only [Sum.elim_inr]
      by_cases hy : y = b
      · subst hy
        rw [hf₂b]
        omega
      · have := hb₂ y hy
        omega
  · rintro (x | x) (y | y) h <;> rw [deleteEdges_adj] at h
    · -- inside the first side
      simp only [Sum.elim_inl]
      by_cases hx : x = a
      · subst hx
        have hy : y ≠ x := fun e => by subst e; exact G₁.irrefl h.1
        rw [hf₁a]
        have := hb₁ y hy
        omega
      · by_cases hy : y = a
        · subst hy
          rw [hf₁a]
          have := hb₁ x hx
          omega
        · rw [hf₁ x hx, hf₁ y hy]
          intro heq
          refine D₁.valid (v := ⟨x, mem_del hx⟩) (w := ⟨y, mem_del hy⟩) ?_ (Fin.ext heq)
          have h1 : G₁.Adj x y := h.1
          simpa [hx, hy] using h1
    · -- first side to second side
      simp only [Sum.elim_inl, Sum.elim_inr]
      by_cases hx : x = a
      · by_cases hy : y = b
        · subst hx
          subst hy
          exact absurd rfl h.2
        · subst hx
          rw [hf₁a]
          have := hb₂ y hy
          omega
      · have := hb₁ x hx
        by_cases hy : y = b
        · subst hy
          rw [hf₂b]
          omega
        · have := hb₂ y hy
          omega
    · -- second side to first side
      simp only [Sum.elim_inl, Sum.elim_inr]
      by_cases hy : y = a
      · by_cases hx : x = b
        · subst hx
          subst hy
          exact absurd Sym2.eq_swap h.2
        · subst hy
          rw [hf₁a]
          have := hb₂ x hx
          omega
      · have := hb₁ y hy
        by_cases hx : x = b
        · subst hx
          rw [hf₂b]
          omega
        · have := hb₂ x hx
          omega
    · -- inside the second side
      simp only [Sum.elim_inr]
      by_cases hx : x = b
      · subst hx
        have hy : y ≠ x := fun e => by subst e; exact G₂.irrefl h.1
        rw [hf₂b]
        have := hb₂ y hy
        omega
      · by_cases hy : y = b
        · subst hy
          rw [hf₂b]
          have := hb₂ x hx
          omega
        · rw [hf₂ x hx, hf₂ y hy]
          intro heq
          refine D₂.valid (v := ⟨x, mem_del hx⟩) (w := ⟨y, mem_del hy⟩) ?_ (Fin.ext (by omega))
          have h1 : G₂.Adj x y := h.1
          simpa [hx, hy] using h1

lemma join_degree_inl [Fintype V] [Fintype W] [DecidableRel G₁.Adj] [DecidableRel (join G₁ G₂).Adj]
    (a : V) : (join G₁ G₂).degree (Sum.inl a) = G₁.degree a + Fintype.card W := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    neighborFinset_eq_filter, neighborFinset_eq_filter, Finset.card_filter, Finset.card_filter,
    Fintype.sum_sum_type]
  simp

lemma join_degree_inr [Fintype V] [Fintype W] [DecidableRel G₂.Adj] [DecidableRel (join G₁ G₂).Adj]
    (b : W) : (join G₁ G₂).degree (Sum.inr b) = G₂.degree b + Fintype.card V := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    neighborFinset_eq_filter, neighborFinset_eq_filter, Finset.card_filter, Finset.card_filter,
    Fintype.sum_sum_type]
  simp [add_comm]

lemma join_ncard [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] [DecidableRel (join G₁ G₂).Adj] :
    (join G₁ G₂).edgeSet.ncard =
      G₁.edgeSet.ncard + G₂.edgeSet.ncard + Fintype.card V * Fintype.card W := by
  rw [← coe_edgeFinset, ← coe_edgeFinset, ← coe_edgeFinset, Set.ncard_coe_finset,
    Set.ncard_coe_finset, Set.ncard_coe_finset]
  have hs := sum_degrees_eq_twice_card_edges (join G₁ G₂)
  have hs₁ := sum_degrees_eq_twice_card_edges G₁
  have hs₂ := sum_degrees_eq_twice_card_edges G₂
  rw [Fintype.sum_sum_type] at hs
  simp only [join_degree_inl, join_degree_inr, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at hs
  rw [Nat.mul_comm (Fintype.card W) (Fintype.card V)] at hs
  generalize Fintype.card V * Fintype.card W = P at hs ⊢
  omega

end main

end OMAStepErdos917H2

open OMAStepErdos917H2 in
theorem OMA.solution : OMA.R_Erdos917_erdos_917_variants_lower_construction_R1.H2 := by
  intro k₁ k₂ n₁ n₂ e₁ e₂ hk₁ hk₂ hG₁ex hG₂ex
  obtain ⟨G₁, hG₁, he₁⟩ := hG₁ex
  obtain ⟨G₂, hG₂, he₂⟩ := hG₂ex
  classical
  have : Nonempty (Fin n₁) := crit_nonempty hG₁ (by omega)
  have : Nonempty (Fin n₂) := crit_nonempty hG₂ (by omega)
  refine ⟨(join G₁ G₂).map finSumFinEquiv.toEmbedding, ?_, ?_⟩
  · refine isKCritical_transport (join G₁ G₂) finSumFinEquiv (by omega)
      (join_colorable (crit_colorable hG₁) (crit_colorable hG₂))
      (join_not_colorable (by omega) (by omega) (crit_not_colorable hG₁ (by omega))
        (crit_not_colorable hG₂ (by omega)))
      join_deg ?_
    rintro (a | a) (b | b) h
    · exact join_edge_inl (by omega) a b (crit_edge hG₁ a b h) (crit_colorable hG₂)
    · exact join_edge_cross (by omega) (by omega) a b (crit_vertex hG₁ a) (crit_vertex hG₂ b)
    · rw [Sym2.eq_swap]
      exact join_edge_cross (by omega) (by omega) b a (crit_vertex hG₁ b) (crit_vertex hG₂ a)
    · exact join_edge_inr (by omega) a b (crit_colorable hG₁) (crit_edge hG₂ a b h)
  · rw [ncard_edgeSet_map, join_ncard, he₁, he₂]
    simp
