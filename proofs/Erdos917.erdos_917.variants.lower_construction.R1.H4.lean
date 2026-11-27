import OMAReductions.R_Erdos917_erdos_917_variants_lower_construction_R1

-- Step Erdos917.erdos_917.variants.lower_construction.R1.H4: hypothesis H4 of reduction Erdos917.erdos_917.variants.lower_construction.R1
-- Credit: @JaviSoto
-- H4 := ∀ n₁ n₂ e₁ e₂ : ℕ, (∃ G : SimpleGraph (Fin (n₁)), Erdos917.IsKCritical G (4) ∧ G.edgeSet.ncard = (e₁)) → (∃ G : SimpleGraph (Fin (n₂)), Erdos917.IsKCritical G (3) ∧ G.edgeSet.ncard = (e₂)) →   (∃ G : SimpleGraph (Fin (2 * n₁ + n₂)), Erdos917.IsKCritical G (5) ∧ G.edgeSet.ncard = (e₁ + e₂ + n₁ + n₁ * n₂))  /-- Joining `r` further odd cycles `C_b` to a `k₀`-critical graph. -/

/-! A construction of a 5-critical graph from 4-critical and 3-critical graphs. -/

open SimpleGraph

namespace OMA.Toft

/-- Original vertices of A, their independent shadows, and the vertices of B. -/
def graph {α β : Type*} (A : SimpleGraph α) (B : SimpleGraph β) :
    SimpleGraph (α ⊕ (α ⊕ β)) where
  Adj x y := match x, y with
    | .inl a, .inl a' => A.Adj a a'
    | .inr (.inr b), .inr (.inr b') => B.Adj b b'
    | .inl a, .inr (.inl s) | .inr (.inl s), .inl a => a = s
    | .inr (.inl _), .inr (.inr _) | .inr (.inr _), .inr (.inl _) => True
    | _, _ => False
  symm := by
    constructor
    rintro (a | s | b) (a' | s' | b') h <;> first | exact h | exact A.adj_symm h | exact B.adj_symm h
  loopless := ⟨by rintro (a | s | b) <;> first | exact A.loopless.irrefl a | exact B.loopless.irrefl b | exact id⟩

lemma neighbor {α β : Type*} [Nonempty α] (A : SimpleGraph α) (B : SimpleGraph β) :
    ∀ v, ∃ w, (graph A B).Adj v w := by
  rintro (a | s | b)
  · exact ⟨.inr (.inl a), rfl⟩
  · exact ⟨.inl s, rfl⟩
  · exact ⟨.inr (.inl (Classical.choice ‹Nonempty α›)), trivial⟩

/-- A coloring after cutting an edge transports across a graph isomorphism. -/
lemma cutColorableIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (i : G ≃g H) {c : ℕ}
    (h : ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).Colorable c) :
    ∀ e ∈ H.edgeSet, (H.deleteEdges {e}).Colorable c := by
  intro e
  induction e using Sym2.inductionOn with
  | _ x y =>
    intro he
    apply (h s(i.symm x, i.symm y) (i.symm.map_rel_iff.mpr he)).of_hom
    refine {toFun := i.symm, map_rel' := ?_}
    intro u v huv
    obtain ⟨hadj, hkeep⟩ := deleteEdges_adj.mp huv
    refine deleteEdges_adj.mpr ⟨i.symm.map_rel_iff.mpr hadj, ?_⟩
    intro hcut
    apply hkeep
    rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hcut) with h | h
    · exact Sym2.eq_iff.mpr (.inl ⟨i.symm.injective h.1, i.symm.injective h.2⟩)
    · exact Sym2.eq_iff.mpr (.inr ⟨i.symm.injective h.1, i.symm.injective h.2⟩)

/-- Vertex deletion factors through deletion of any incident edge. -/
lemma vertexDeletionLeEdge {V : Type*} (G : SimpleGraph V) (v w : V) :
    ((⊤ : G.Subgraph).deleteVerts {v}).coe.chromaticNumber ≤
      (G.deleteEdges {s(v, w)}).chromaticNumber := by
  apply chromaticNumber_mono_of_hom
  refine { toFun := Subtype.val, map_rel' := ?_ }
  intro a b hab
  refine deleteEdges_adj.mpr ⟨((⊤ : G.Subgraph).deleteVerts {v}).adj_sub hab, ?_⟩
  intro he
  rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp he) with h | h
  · exact a.property.2 h.1
  · exact b.property.2 h.2

lemma criticalOfCuts {V : Type*} (G : SimpleGraph V) (hχ : G.chromaticNumber = 5)
    (hne : ∀ v, ∃ w, G.Adj v w)
    (hcut : ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).Colorable 4) :
    Erdos917.IsKCritical G 5 := by
  have he : ∀ e ∈ G.edgeSet, G.IsCriticalEdge e := by
    intro e hm
    unfold IsCriticalEdge IsCriticalEdges
    rw [hχ]
    exact (hcut e hm).chromaticNumber_le.trans_lt (by decide)
  refine ⟨⟨hχ, ?_⟩, he⟩
  intro v
  obtain ⟨w, hw⟩ := hne v
  unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts
  rw [chromaticNumber_congr Subgraph.topIso]
  exact (vertexDeletionLeEdge G v w).trans_lt (he s(v,w) hw)

lemma realize {V : Type*} {n : ℕ} (e : V ≃ Fin n) (G : SimpleGraph V)
    (hχ : G.chromaticNumber = 5) (hn : ∀ v, ∃ w, G.Adj v w)
    (hcut : ∀ a ∈ G.edgeSet, (G.deleteEdges {a}).Colorable 4) :
    ∃ H : SimpleGraph (Fin n), Erdos917.IsKCritical H 5 ∧ H.edgeSet.ncard = G.edgeSet.ncard := by
  let H := G.map e
  let i : G ≃g H := Iso.map e G
  refine ⟨H, criticalOfCuts H ((chromaticNumber_congr i).symm.trans hχ) ?_
    (cutColorableIso i hcut), (Set.ncard_congr' i.mapEdgeSet).symm⟩
  intro v
  obtain ⟨w, hw⟩ := hn (i.symm v)
  exact ⟨i w, by simpa using i.map_rel_iff.mpr hw⟩


lemma graphColorableFive {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β}
    (hA : A.Colorable 4) (hB : B.Colorable 3) : (graph A B).Colorable 5 := by
  obtain ⟨ca⟩ := hA
  obtain ⟨cb⟩ := hB.mono (show 3 ≤ 4 by decide)
  refine ⟨Coloring.mk (fun
    | .inl a => (ca a).castSucc
    | .inr (.inl _) => Fin.last 4
    | .inr (.inr b) => (cb b).castSucc) ?_⟩
  rintro (a | s | b) (a' | s' | b') hab <;> first
    | exact (Fin.castSucc_injective _).ne (ca.valid hab)
    | exact (Fin.castSucc_injective _).ne (cb.valid hab)
    | exact Fin.castSucc_ne_last _
    | exact (Fin.castSucc_ne_last _).symm
    | exact hab.elim

lemma graphNotColorableFour {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β}
    (hA : A.chromaticNumber = 4) (hB : B.chromaticNumber = 3) :
    ¬(graph A B).Colorable 4 := by
  rintro ⟨c⟩
  let ca : A.Coloring (Fin 4) := Coloring.mk (fun a => c (.inl a))
    (fun {_ _} h => c.valid h)
  let shadow (a : α) := c (.inr (.inl a))
  have surj : Function.Surjective ca :=
    le_chromaticNumber_iff_forall_surjective.mp hA.ge ca
  obtain ⟨a₀, _⟩ := surj 0
  obtain ⟨a, ha⟩ := surj (shadow a₀)
  have hdiff : shadow a ≠ shadow a₀ := by
    rw [← ha]
    exact (c.valid (show (graph A B).Adj (.inl a) (.inr (.inl a)) from rfl)).symm
  let S := {i : Fin 4 // i ≠ shadow a ∧ i ≠ shadow a₀}
  let cb : B.Coloring S := Coloring.mk (fun b =>
    ⟨c (.inr (.inr b)),
      c.valid (show (graph A B).Adj (.inr (.inr b)) (.inr (.inl a)) from trivial),
      c.valid (show (graph A B).Adj (.inr (.inr b)) (.inr (.inl a₀)) from trivial)⟩)
    (fun {b b'} h eq => c.valid
      (show (graph A B).Adj (.inr (.inr b)) (.inr (.inr b')) from h)
      (congrArg Subtype.val eq))
  have hcard (x y : Fin 4) (hne : x ≠ y) :
      Fintype.card {i : Fin 4 // i ≠ x ∧ i ≠ y} = 2 := by
    fin_cases x <;> fin_cases y <;> first | contradiction | decide
  have hle := cb.colorable.chromaticNumber_le
  rw [hB, show Fintype.card S = 2 from hcard _ _ hdiff] at hle
  norm_num at hle

lemma graphChromaticNumber {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β}
    (hA : A.chromaticNumber = 4) (hB : B.chromaticNumber = 3) :
    (graph A B).chromaticNumber = 5 := by
  apply (chromaticNumber_eq_iff_colorable_not_colorable (n := 4)).mpr
  exact ⟨graphColorableFive (chromaticNumber_le_iff_colorable.mp hA.le)
    (chromaticNumber_le_iff_colorable.mp hB.le), graphNotColorableFour hA hB⟩

lemma degree_as_neighbor_sum {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : G.degree v = ∑ w, if G.Adj v w then 1 else 0 := by
  simp [SimpleGraph.degree, G.neighborFinset_eq_filter]

lemma graph_edge_count {α β : Type*} [Fintype α] [Fintype β]
    (A : SimpleGraph α) (B : SimpleGraph β) :
    (graph A B).edgeSet.ncard = A.edgeSet.ncard + B.edgeSet.ncard + Fintype.card α +
      Fintype.card α * Fintype.card β := by
  classical
  have weight (v w : α ⊕ (α ⊕ β)) :
      (if (graph A B).Adj v w then 1 else 0 : ℕ) =
        match v, w with
        | .inl a, .inl a' => if A.Adj a a' then 1 else 0
        | .inr (.inr b), .inr (.inr b') => if B.Adj b b' then 1 else 0
        | .inl a, .inr (.inl s) | .inr (.inl s), .inl a => if a = s then 1 else 0
        | .inr (.inl _), .inr (.inr _) | .inr (.inr _), .inr (.inl _) => 1
        | _, _ => 0 := by
    rcases v with a | s | b <;> rcases w with a' | s' | b' <;>
      simp only [graph] <;> split_ifs <;> simp_all
  have ha (a : α) : (graph A B).degree (.inl a) = A.degree a + 1 := by
    rw [degree_as_neighbor_sum, degree_as_neighbor_sum A]
    simp [Fintype.sum_sum_type, weight]
  have hs (a : α) : (graph A B).degree (.inr (.inl a)) = 1 + Fintype.card β := by
    rw [degree_as_neighbor_sum]
    simp [Fintype.sum_sum_type, weight]
  have hb (b : β) : (graph A B).degree (.inr (.inr b)) = Fintype.card α + B.degree b := by
    rw [degree_as_neighbor_sum, degree_as_neighbor_sum B]
    simp [Fintype.sum_sum_type, weight]
  have hG := (graph A B).sum_degrees_eq_twice_card_edges
  simp only [Fintype.sum_sum_type, ha, hs, hb, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    A.sum_degrees_eq_twice_card_edges, B.sum_degrees_eq_twice_card_edges] at hG
  simp only [Set.ncard_eq_toFinset_card']
  change (graph A B).edgeFinset.card = A.edgeFinset.card + B.edgeFinset.card + _ + _
  nlinarith [hG]

lemma edgeColorDrop {α : Type*} {G : SimpleGraph α} {k : ℕ}
    (hG : Erdos917.IsKCritical G (k + 1)) {x y : α} (hxy : G.Adj x y) :
    (G.deleteEdges ({s(x,y)} : Set _)).Colorable k := by
  have h := hG.2 s(x,y) hxy
  change (G.deleteEdges _).chromaticNumber < G.chromaticNumber at h
  rw [hG.1.1, Nat.cast_add, Nat.cast_one] at h
  exact chromaticNumber_le_iff_colorable.mp (Order.le_of_lt_add_one h)

lemma markedColor {α : Type*} {G : SimpleGraph α} {k : ℕ}
    (hG : Erdos917.IsKCritical G (k + 1)) (v : α) :
    ∃ c : G.Coloring (Fin (k + 1)), ∀ x, c x = Fin.last k ↔ x = v := by
  classical
  let S := (⊤ : G.Subgraph).deleteVerts {v}
  have h := hG.1.2 v
  change S.coe.chromaticNumber < (⊤ : G.Subgraph).coe.chromaticNumber at h
  rw [chromaticNumber_congr (Subgraph.topIso (G := G)), hG.1.1, Nat.cast_add, Nat.cast_one] at h
  obtain ⟨f⟩ := chromaticNumber_le_iff_colorable.mp (Order.le_of_lt_add_one h)
  let c (x : α) : Fin (k + 1) := if hx : x = v then Fin.last k else
    (f ⟨x, by exact ⟨Set.mem_univ _, hx⟩⟩).castSucc
  refine ⟨Coloring.mk c ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x = v <;> by_cases hy : y = v
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · simp [c, hx, hy, Ne.symm (Fin.castSucc_ne_last _)]
    · simp [c, hx, hy, Fin.castSucc_ne_last]
    · simp only [c, dif_neg hx, dif_neg hy, ne_eq, Fin.castSucc_inj]
      apply f.valid
      change S.Adj x y
      exact Subgraph.deleteVerts_adj.mpr ⟨Set.mem_univ _, hx, Set.mem_univ _, hy, hxy⟩
  · intro x
    change c x = Fin.last k ↔ x = v
    by_cases hx : x = v <;> simp [c, hx, Fin.castSucc_ne_last]

lemma assembleCut {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β}
    (e : Sym2 (α ⊕ (α ⊕ β))) (a s : α → Fin 4) (b : β → Fin 4)
    (ha : ∀ x y, A.Adj x y → s(Sum.inl x, Sum.inl y) ≠ e → a x ≠ a y)
    (hb : ∀ x y, B.Adj x y → s(Sum.inr (Sum.inr x), Sum.inr (Sum.inr y)) ≠ e → b x ≠ b y)
    (hm : ∀ x, s(Sum.inl x, Sum.inr (Sum.inl x)) ≠ e → a x ≠ s x)
    (hc : ∀ x y, s(Sum.inr (Sum.inl x), Sum.inr (Sum.inr y)) ≠ e → s x ≠ b y) :
    ((graph A B).deleteEdges {e}).Colorable 4 := by
  refine ⟨Coloring.mk (Sum.elim a (Sum.elim s b)) ?_⟩
  rintro (x | x | x) (y | y | y) h <;> obtain ⟨h, hn⟩ := deleteEdges_adj.mp h
  · exact ha _ _ h hn
  · change x = y at h
    subst y
    exact hm _ hn
  · exact h.elim
  · change y = x at h
    subst y
    exact (hm _ (fun hh => hn (Sym2.eq_swap.trans hh))).symm
  · exact h.elim
  · exact hc _ _ hn
  · exact h.elim
  · exact (hc _ _ (fun hh => hn (Sym2.eq_swap.trans hh))).symm
  · exact hb _ _ h hn

lemma cutOriginal {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β}
    (hA : Erdos917.IsKCritical A 4) (hB : Erdos917.IsKCritical B 3)
    {x y : α} (hxy : A.Adj x y) :
    ((graph A B).deleteEdges {s(Sum.inl x, Sum.inl y)}).Colorable 4 := by
  obtain ⟨a⟩ := edgeColorDrop (k := 3) hA hxy
  obtain ⟨b⟩ := chromaticNumber_le_iff_colorable.mp (le_of_eq hB.1.1)
  apply assembleCut _ (fun u => (a u).castSucc) (fun _ => Fin.last 3) (fun u => (b u).castSucc)
  · intro u v huv hn
    apply (Fin.castSucc_injective _).ne
    apply a.valid
    apply deleteEdges_adj.mpr
    refine ⟨huv, ?_⟩
    intro h
    apply hn
    have eq : s(u,v) = s(x,y) := h
    simpa using congrArg (Sym2.map (Sum.inl : α → α ⊕ (α ⊕ β))) eq
  · exact fun _ _ huv _ => (Fin.castSucc_injective _).ne (b.valid huv)
  · exact fun _ _ => Fin.castSucc_ne_last _
  · exact fun _ _ _ => (Fin.castSucc_ne_last _).symm

lemma cutRight {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β}
    (hA : Erdos917.IsKCritical A 4) (hB : Erdos917.IsKCritical B 3)
    {x y : β} (hxy : B.Adj x y) :
    ((graph A B).deleteEdges {s(Sum.inr (Sum.inr x), Sum.inr (Sum.inr y))}).Colorable 4 := by
  obtain ⟨a⟩ := chromaticNumber_le_iff_colorable.mp (le_of_eq hA.1.1)
  obtain ⟨b⟩ := edgeColorDrop (k := 2) hB hxy
  let spare (u : α) : Fin 4 := if a u = 3 then 2 else 3
  apply assembleCut _ a spare (fun u => (b u).castSucc.castSucc)
  · exact fun _ _ huv _ => a.valid huv
  · intro u v huv hn
    apply (Fin.castSucc_injective _).ne
    apply (Fin.castSucc_injective _).ne
    apply b.valid
    apply deleteEdges_adj.mpr
    refine ⟨huv, ?_⟩
    intro h
    apply hn
    have eq : s(u,v) = s(x,y) := h
    simpa using congrArg (Sym2.map (fun w : β => (Sum.inr (Sum.inr w) : α ⊕ (α ⊕ β)))) eq
  · intro u _
    dsimp [spare]
    split <;> rename_i h
    · rw [h]; decide
    · exact h
  · intro u v _
    have hlt := (b v).isLt
    dsimp [spare]
    split <;> intro h <;> have hv := congrArg Fin.val h <;>
      simp at hv <;> omega

lemma cutMatch {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β}
    (hA : Erdos917.IsKCritical A 4) (hB : Erdos917.IsKCritical B 3) (v : α) :
    ((graph A B).deleteEdges {s(Sum.inl v, Sum.inr (Sum.inl v))}).Colorable 4 := by
  obtain ⟨a, mark⟩ := markedColor (k := 3) hA v
  obtain ⟨b⟩ := chromaticNumber_le_iff_colorable.mp (le_of_eq hB.1.1)
  apply assembleCut _ a (fun _ => Fin.last 3) (fun x => (b x).castSucc)
  · exact fun _ _ h _ => a.valid h
  · exact fun _ _ h _ => (Fin.castSucc_injective _).ne (b.valid h)
  · intro x hn hx
    exact hn (by rw [(mark _).mp hx])
  · exact fun _ _ _ => (Fin.castSucc_ne_last _).symm

lemma cutCross {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β}
    (hA : Erdos917.IsKCritical A 4) (hB : Erdos917.IsKCritical B 3) (u : α) (v : β) :
    ((graph A B).deleteEdges {s(Sum.inr (Sum.inl u), Sum.inr (Sum.inr v))}).Colorable 4 := by
  classical
  obtain ⟨a, ma⟩ := markedColor (k := 3) hA u
  obtain ⟨b, mb⟩ := markedColor (k := 2) hB v
  let sh (x : α) := if x = u then (Fin.last 2).castSucc else Fin.last 3
  apply assembleCut _ a sh (fun x => (b x).castSucc)
  · exact fun _ _ h _ => a.valid h
  · exact fun _ _ h _ => (Fin.castSucc_injective _).ne (b.valid h)
  · intro x _
    by_cases h : x = u
    · simp [sh, h, (ma u).mpr rfl]
    · simpa [sh, h] using (mt (ma x).mp h)
  · intro x y hn
    by_cases h : x = u
    · rw [show sh x = (Fin.last 2).castSucc by simp [sh, h]]
      exact (Fin.castSucc_injective _).ne (Ne.symm (mt (mb y).mp (fun hy => hn (by rw [h, hy]))))
    · simpa [sh, h] using (Fin.castSucc_ne_last (b y)).symm

lemma edgeFourColorable {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β}
    (hA : Erdos917.IsKCritical A 4) (hB : Erdos917.IsKCritical B 3)
    (e : Sym2 (α ⊕ (α ⊕ β))) (he : e ∈ (graph A B).edgeSet) :
    ((graph A B).deleteEdges {e}).Colorable 4 := by
  induction e using Sym2.inductionOn with
  | _ x y =>
    rcases x with x | x | x <;> rcases y with y | y | y
    · exact cutOriginal hA hB he
    · change x = y at he
      subst y
      exact cutMatch hA hB x
    · exact he.elim
    · change y = x at he
      subst y
      rw [Sym2.eq_swap]
      exact cutMatch hA hB x
    · exact he.elim
    · exact cutCross hA hB x y
    · exact he.elim
    · rw [Sym2.eq_swap]
      exact cutCross hA hB y x
    · exact cutRight hA hB he

end OMA.Toft

theorem OMA.solution : OMA.R_Erdos917_erdos_917_variants_lower_construction_R1.H4 := by
  classical
  rintro n₁ n₂ e₁ e₂ ⟨A, hA, eA⟩ ⟨B, hB, eB⟩
  have hbound := A.chromaticNumber_le_card
  rw [hA.1.1, Fintype.card_fin] at hbound
  have hn₁ : 4 ≤ n₁ := by exact_mod_cast hbound
  let : Nonempty (Fin n₁) := ⟨⟨0, by omega⟩⟩
  let e : Fin n₁ ⊕ (Fin n₁ ⊕ Fin n₂) ≃ Fin (2 * n₁ + n₂) :=
    Fintype.equivFinOfCardEq (by simp; omega)
  obtain ⟨H, hH, hsize⟩ := OMA.Toft.realize e (OMA.Toft.graph A B)
    (OMA.Toft.graphChromaticNumber hA.1.1 hB.1.1) (OMA.Toft.neighbor A B)
    (OMA.Toft.edgeFourColorable hA hB)
  refine ⟨H, hH, hsize.trans ?_⟩
  simpa [eA, eB] using OMA.Toft.graph_edge_count A B
