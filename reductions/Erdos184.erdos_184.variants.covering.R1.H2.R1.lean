import OMAReductions.R_Erdos184_erdos_184_variants_covering_R1
import Mathlib

/-!
# Reduction to Eulerian cycle covers and subdivision suppression

Credit: @Heart-galaxy
Fan source: https://doi.org/10.1016/S0095-8956(03)00068-6

Take a spanning even subgraph with as many edges as possible. Its complement is a forest.
Keep the original graph and add a length-two path along each edge of that forest. This yields
an Eulerian graph with at most twice as many vertices minus one. An Eulerian cycle cover (`H1`)
therefore has the required budget. Cut each cycle at an original vertex, compress the
remaining path using `H2`, and close it to get a cycle or a single edge. The connected-component
bounds then add.
-/

open SimpleGraph

namespace OMA.R_Erdos184_erdos_184_variants_covering_R1_H2_R1

/-- Cover a connected even graph by at most half as many cycles as vertices. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → (∀ v, Even ((G.neighborSet v).ncard)) →
    ∃ S : Finset (Finset (Sym2 V)),
      (∀ s ∈ S, ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) ∧
      (∀ e ∈ G.edgeSet, ∃ s ∈ S, e ∈ s) ∧ S.card ≤ Fintype.card V / 2

/-- A simple path between original vertices can suppress the added vertices while
retaining all its original edges. -/
def H2 : Prop :=
  ∀ (V : Type) (G F : SimpleGraph V) (A : SimpleGraph (V ⊕ F.edgeSet)),
    F ≤ G →
    (∀ v w : V, A.Adj (.inl v) (.inl w) ↔ G.Adj v w) →
    (∀ (v : V) (e : F.edgeSet), A.Adj (.inl v) (.inr e) ↔ v ∈ (e.val : Sym2 V)) →
    (∀ e f : F.edgeSet, ¬ A.Adj (.inr e) (.inr f)) →
    ∀ (u v : V) (p : A.Walk (.inl u) (.inl v)), p.IsPath →
      ∃ q : G.Walk u v, q.IsPath ∧ ∀ e : Sym2 V, Sym2.map Sum.inl e ∈ p.edges → e ∈ q.edges

section Components

private theorem cover_piece_image {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H) (hf : Function.Injective f)
    {s : Finset (Sym2 V)} (hs : (∃ e ∈ G.edgeSet, s = {e}) ∨
      ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) :
    (∃ e ∈ H.edgeSet, s.image (Sym2.map f) = {e}) ∨
      ∃ (u : W) (p : H.Walk u u), p.IsCycle ∧ s.image (Sym2.map f) = p.edges.toFinset := by
  rcases hs with ⟨e, he, rfl⟩ | ⟨u, p, hp, rfl⟩
  · exact Or.inl ⟨_, f.map_mem_edgeSet he, Finset.image_singleton _ _⟩
  · refine Or.inr ⟨f u, p.map f, hp.map hf, ?_⟩
    rw [Walk.edges_map]
    ext e
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]

private theorem sum_card_component {V : Type} [Fintype V] (G : SimpleGraph V)
    [Fintype G.ConnectedComponent] [∀ c : G.ConnectedComponent, Fintype c] :
    (∑ c : G.ConnectedComponent, Fintype.card c) = Fintype.card V := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv G.connectedComponentMk)

/-- A connected-case covering theorem gives the stated budget on all graphs. -/
private theorem of_connected
    (h : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → ∃ S : Finset (Finset (Sym2 V)),
        (∀ s ∈ S, (∃ e ∈ G.edgeSet, s = {e}) ∨
          ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) ∧
        (∀ e ∈ G.edgeSet, ∃ s ∈ S, e ∈ s) ∧
        S.card + 1 ≤ Fintype.card V) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ S : Finset (Finset (Sym2 V)),
        (∀ s ∈ S, (∃ e ∈ G.edgeSet, s = {e}) ∨
          ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) ∧
        (∀ e ∈ G.edgeSet, ∃ s ∈ S, e ∈ s) ∧
        S.card + Nat.card G.ConnectedComponent ≤ Fintype.card V := by
  intro V _ _ G
  classical
  choose S hpieces hcover hsize using fun (c : G.ConnectedComponent) =>
    h c c.toSimpleGraph c.connected_toSimpleGraph
  let L (c : G.ConnectedComponent) : Finset (Finset (Sym2 V)) :=
    (S c).image (fun s => s.image (Sym2.map c.toSimpleGraph_hom))
  let U := Finset.univ.biUnion L
  refine ⟨U, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨c, _, hcs⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hcs
    exact cover_piece_image c.toSimpleGraph_hom Subtype.val_injective (hpieces c t ht)
  · intro e he
    induction e using Sym2.ind with
    | h v w =>
      have hvw : G.Adj v w := by simpa using he
      let c := G.connectedComponentMk v
      let v' : c := ⟨v, rfl⟩
      let w' : c := ⟨w, c.mem_supp_of_adj_mem_supp (u := v) rfl hvw⟩
      have he' : s(v', w') ∈ c.toSimpleGraph.edgeSet := hvw
      obtain ⟨t, ht, he'⟩ := hcover c _ he'
      refine ⟨t.image (Sym2.map c.toSimpleGraph_hom), ?_, ?_⟩
      · exact Finset.mem_biUnion.mpr
          ⟨c, Finset.mem_univ _, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩
      · exact Finset.mem_image.mpr ⟨s(v', w'), he', rfl⟩
  · have hcardU : U.card ≤ ∑ c : G.ConnectedComponent, (S c).card :=
      Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun _ _ => Finset.card_image_le
    calc
      U.card + Nat.card G.ConnectedComponent ≤
          (∑ c : G.ConnectedComponent, (S c).card) + (∑ _ : G.ConnectedComponent, 1) := by
        simpa [Nat.card_eq_fintype_card] using hcardU
      _ = ∑ c : G.ConnectedComponent, ((S c).card + 1) := Finset.sum_add_distrib.symm
      _ ≤ ∑ c : G.ConnectedComponent, Fintype.card c :=
        Finset.sum_le_sum fun c _ => hsize c
      _ = Fintype.card V := sum_card_component G

end Components

private theorem exists_augmentation {V : Type} (G F : SimpleGraph V) :
    ∃ A : SimpleGraph (V ⊕ F.edgeSet),
      (∀ v w : V, A.Adj (.inl v) (.inl w) ↔ G.Adj v w) ∧
      (∀ (v : V) (e : F.edgeSet), A.Adj (.inl v) (.inr e) ↔ v ∈ (e.val : Sym2 V)) ∧
      (∀ e f : F.edgeSet, ¬ A.Adj (.inr e) (.inr f)) := by
  let adj : V ⊕ F.edgeSet → V ⊕ F.edgeSet → Prop := fun
    | .inl v, .inl w => G.Adj v w
    | .inl v, .inr e => v ∈ (e.val : Sym2 V)
    | .inr e, .inl v => v ∈ (e.val : Sym2 V)
    | .inr _, .inr _ => False
  let A : SimpleGraph (V ⊕ F.edgeSet) := {
    Adj := adj
    symm := by
      constructor
      intro u v huv
      cases u <;> cases v
      · exact G.adj_symm huv
      · exact huv
      · exact huv
      · exact huv
    loopless := by
      constructor
      intro v hv
      cases v with
      | inl u => exact G.loopless.irrefl u hv
      | inr e => exact hv }
  exact ⟨A, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => id⟩

section Augmentation

variable {V : Type} {G F : SimpleGraph V} {A : SimpleGraph (V ⊕ F.edgeSet)}
  (hOld : ∀ v w : V, A.Adj (.inl v) (.inl w) ↔ G.Adj v w)
  (hCross : ∀ (v : V) (e : F.edgeSet), A.Adj (.inl v) (.inr e) ↔ v ∈ (e.val : Sym2 V))
  (hNew : ∀ e f : F.edgeSet, ¬ A.Adj (.inr e) (.inr f))

include hOld hCross in
private theorem augment_ncard_old [Finite V] (v : V) :
    (A.neighborSet (.inl v)).ncard =
      (G.neighborSet v).ncard + (F.neighborSet v).ncard := by
  classical
  let eqv : A.neighborSet (.inl v) ≃ (G.neighborSet v ⊕ F.incidenceSet v) := {
    toFun := fun
      | ⟨.inl w, hw⟩ => .inl ⟨w, (hOld v w).mp hw⟩
      | ⟨.inr e, he⟩ => .inr ⟨e.val, ⟨e.property, (hCross v e).mp he⟩⟩
    invFun := fun
      | .inl w => ⟨.inl w.val, (hOld v w).mpr w.property⟩
      | .inr e => ⟨.inr ⟨e.val, e.property.1⟩, (hCross v _).mpr e.property.2⟩
    left_inv := by rintro ⟨w, hw⟩; cases w <;> rfl
    right_inv := by intro w; cases w <;> rfl }
  simp only [← Nat.card_coe_set_eq]
  rw [Nat.card_congr eqv, Nat.card_sum, Nat.card_congr (F.incidenceSetEquivNeighborSet v)]

include hCross hNew in
private theorem augment_ncard_new (e : F.edgeSet) :
    (A.neighborSet (.inr e)).ncard = 2 := by
  classical
  let eqv : A.neighborSet (.inr e) ≃ {v : V // v ∈ (e.val : Sym2 V)} := {
    toFun := fun
      | ⟨.inl v, hv⟩ => ⟨v, (hCross v e).mp hv.symm⟩
      | ⟨.inr f, hf⟩ => False.elim (hNew e f hf)
    invFun := fun v => ⟨.inl v.val, ((hCross v.val e).mpr v.property).symm⟩
    left_inv := by
      rintro ⟨w, hw⟩
      cases w with
      | inl => rfl
      | inr f => exact False.elim (hNew e f hw)
    right_inv := by intro v; rfl }
  rw [← Nat.card_coe_set_eq, Nat.card_congr eqv]
  have h : (↑e.val.toFinset : Set V) = {v | v ∈ (e.val : Sym2 V)} := by ext v; simp
  change Nat.card ↥{v : V | v ∈ (e.val : Sym2 V)} = 2
  rw [← h, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  exact e.val.card_toFinset_of_not_isDiag (F.not_isDiag_of_mem_edgeSet e.property)

include hOld hCross hNew in
private theorem augment_even [Finite V] {E : SimpleGraph V} (hEG : E ≤ G)
    (hE : ∀ v, Even ((E.neighborSet v).ncard)) (hF : F = G \ E)
    (z : V ⊕ F.edgeSet) : Even ((A.neighborSet z).ncard) := by
  cases z with
  | inr e => rw [augment_ncard_new hCross hNew]; exact even_two
  | inl v =>
    have hsup : E ⊔ F = G := by rw [hF, sup_sdiff_cancel_right hEG]
    have hdisj : Disjoint E F := by rw [hF]; exact disjoint_sdiff_self_right
    have hdegree : (G.neighborSet v).ncard = (E.neighborSet v).ncard + (F.neighborSet v).ncard := by
      rw [← hsup, neighborSet_sup, Set.ncard_union_eq (disjoint_neighborSet.mpr hdisj v)]
    rw [augment_ncard_old hOld hCross, hdegree, add_assoc]
    exact (hE v).add ⟨_, rfl⟩

include hOld hCross in
private theorem augment_connected (hG : G.Connected) : A.Connected := by
  let f : G →g A := ⟨Sum.inl, fun {_ _} h => (hOld _ _).mpr h⟩
  have hold (z : V ⊕ F.edgeSet) : ∃ v : V, A.Reachable z (.inl v) := by
    cases z with
    | inl v => exact ⟨v, Reachable.rfl⟩
    | inr e =>
      have he (s : Sym2 V) : ∃ v, v ∈ s := by
        induction s using Sym2.ind with
        | h v w => exact ⟨v, by simp⟩
      obtain ⟨v, hv⟩ := he e.val
      exact ⟨v, ((hCross v e).mpr hv).symm.reachable⟩
  refine { preconnected := ?_, nonempty := hG.nonempty.map Sum.inl }
  intro x y
  obtain ⟨u, hu⟩ := hold x
  obtain ⟨v, hv⟩ := hold y
  exact hu.trans (((hG.preconnected u v).map f).trans hv.symm)

end Augmentation

private theorem close_path_cover_piece {V : Type} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (p : G.Walk v u) (hp : p.IsPath) :
    ∃ s : Finset (Sym2 V), ((∃ e ∈ G.edgeSet, s = {e}) ∨
      ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) ∧ s(u,v) ∈ s ∧ ∀ e ∈ p.edges, e ∈ s := by
  by_cases he : s(u,v) ∈ p.edges
  · refine ⟨{s(u,v)}, Or.inl ⟨s(u,v), huv, rfl⟩, Finset.mem_singleton_self _, ?_⟩
    have hp' := hp.eq_adj_toWalk_of_mem_edges (by simpa only [Sym2.eq_swap] using he :
      s(v,u) ∈ p.edges)
    intro e he
    simpa [hp', Sym2.eq_swap] using he
  · let c := Walk.cons huv p
    have hc : c.IsCycle := (Walk.cons_isCycle_iff p huv).mpr ⟨hp, he⟩
    refine ⟨c.edges.toFinset, Or.inr ⟨u, c, hc, rfl⟩, by simp [c], ?_⟩
    intro e he
    exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ he)

private theorem old_edge_ne_mixed {V : Type} {F : SimpleGraph V} (e : Sym2 V)
    (v : V) (f : F.edgeSet) : Sym2.map Sum.inl e ≠ s(Sum.inl v, Sum.inr f) := by
  induction e using Sym2.ind with
  | h x y => simp [Sym2.map_mk]

section Suppression

variable {V : Type} {G F : SimpleGraph V} {A : SimpleGraph (V ⊕ F.edgeSet)}
  (hOld : ∀ v w : V, A.Adj (.inl v) (.inl w) ↔ G.Adj v w)
  (hCross : ∀ (v : V) (e : F.edgeSet), A.Adj (.inl v) (.inr e) ↔ v ∈ (e.val : Sym2 V))
  (hNew : ∀ e f : F.edgeSet, ¬ A.Adj (.inr e) (.inr f))

include hNew in
private theorem cycle_has_old_vertex {z : V ⊕ F.edgeSet}
    (p : A.Walk z z) (hp : p.IsCycle) : ∃ u : V, Sum.inl u ∈ p.support := by
  cases z with
  | inl u => exact ⟨u, p.start_mem_support⟩
  | inr e =>
    cases p with
    | nil => exact (Walk.not_isCycle_nil hp).elim
    | @cons _ z _ hadj q =>
      cases z with
      | inl u => exact ⟨u, by simp⟩
      | inr f => exact (hNew e f hadj).elim

include hOld hCross hNew in
private theorem suppress_of_path_compression [DecidableEq V] (hCompress : H2) (hFG : F ≤ G)
    (z : V ⊕ F.edgeSet) (p : A.Walk z z) (hp : p.IsCycle) :
    ∃ s : Finset (Sym2 V), ((∃ e ∈ G.edgeSet, s = {e}) ∨
      ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) ∧
      ∀ e : Sym2 V, Sym2.map Sum.inl e ∈ p.edges → e ∈ s := by
  have hold (u : V) (c : A.Walk (.inl u) (.inl u)) (hc : c.IsCycle) :
      ∃ s : Finset (Sym2 V), ((∃ e ∈ G.edgeSet, s = {e}) ∨
      ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) ∧
        ∀ e : Sym2 V, Sym2.map Sum.inl e ∈ c.edges → e ∈ s := by
    cases c with
    | nil => exact (Walk.not_isCycle_nil hc).elim
    | @cons _ z _ h q =>
      obtain ⟨hq, hnone⟩ := (Walk.cons_isCycle_iff q h).mp hc
      cases z with
      | inl v =>
        obtain ⟨r, hr, hpres⟩ := hCompress V G F A hFG hOld hCross hNew v u q hq
        obtain ⟨s, hs, hedge, hcover⟩ := close_path_cover_piece
          ((hOld u v).mp h) r hr
        refine ⟨s, hs, ?_⟩
        intro e he
        rcases List.mem_cons.mp he with he | he
        · have he' : e = s(u,v) := Sym2.map.injective Sum.inl_injective he
          exact he' ▸ hedge
        · exact hcover e (hpres e he)
      | inr f =>
        cases q with
        | @cons _ z _ h' q' =>
          cases z with
          | inr g => exact (hNew f g h').elim
          | inl v =>
            have hne : u ≠ v := by
              intro eq
              subst v
              exact hnone (List.mem_cons.mpr (Or.inl Sym2.eq_swap))
            have huv : G.Adj u v := hFG (F.adj_of_mem_incidenceSet hne
              ⟨f.property, (hCross u f).mp h⟩
              ⟨f.property, (hCross v f).mp h'.symm⟩)
            have hq' : q'.IsPath := hq.of_cons
            obtain ⟨r, hr, hpres⟩ := hCompress V G F A hFG hOld hCross hNew v u q' hq'
            obtain ⟨s, hs, _, hcover⟩ := close_path_cover_piece huv r hr
            refine ⟨s, hs, ?_⟩
            intro e he
            rcases List.mem_cons.mp he with he | he
            · exact (old_edge_ne_mixed e u f he).elim
            rcases List.mem_cons.mp he with he | he
            · exact (old_edge_ne_mixed e v f (he.trans Sym2.eq_swap)).elim
            · exact hcover e (hpres e he)
  obtain ⟨u, hu⟩ := cycle_has_old_vertex hNew p hp
  obtain ⟨s, hs, hpres⟩ := hold u (p.rotate (.inl u) hu) (hp.rotate hu)
  exact ⟨s, hs, fun e he => hpres e ((p.rotate_edges (.inl u) hu).perm.mem_iff.mpr he)⟩

include hOld hCross hNew in
private theorem cover_of_augment [DecidableEq V] [DecidableEq (V ⊕ F.edgeSet)]
    (hCompress : H2) (hFG : F ≤ G)
    (S : Finset (Finset (Sym2 (V ⊕ F.edgeSet))))
    (hgood : ∀ s ∈ S, ∃ (u : V ⊕ F.edgeSet) (p : A.Walk u u), p.IsCycle ∧ s = p.edges.toFinset)
    (hcover : ∀ e ∈ A.edgeSet, ∃ s ∈ S, e ∈ s) :
    ∃ T : Finset (Finset (Sym2 V)),
      (∀ s ∈ T, (∃ e ∈ G.edgeSet, s = {e}) ∨
        ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) ∧
      (∀ e ∈ G.edgeSet, ∃ s ∈ T, e ∈ s) ∧ T.card ≤ S.card := by
  classical
  have hpiece (t : S) : ∃ s : Finset (Sym2 V), ((∃ e ∈ G.edgeSet, s = {e}) ∨
      ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) ∧
      ∀ e : Sym2 V, Sym2.map Sum.inl e ∈ t.val → e ∈ s := by
    obtain ⟨u, p, hp, ht⟩ := hgood t.val t.property
    obtain ⟨s, hs, hpreserve⟩ := suppress_of_path_compression hOld hCross hNew hCompress hFG u p hp
    refine ⟨s, hs, ?_⟩
    intro e he
    exact hpreserve e (List.mem_toFinset.mp (ht ▸ he))
  choose f hf using hpiece
  refine ⟨S.attach.image f, ?_, ?_, Finset.card_image_le.trans_eq Finset.card_attach⟩
  · intro s hs
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
    exact (hf t).1
  · intro e he
    let embed : G →g A := ⟨Sum.inl, fun {_ _} h => (hOld _ _).mpr h⟩
    have hplus : Sym2.map Sum.inl e ∈ A.edgeSet := embed.map_mem_edgeSet he
    obtain ⟨t, ht, het⟩ := hcover _ hplus
    exact ⟨f ⟨t, ht⟩, Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩,
      (hf ⟨t, ht⟩).2 e het⟩

end Suppression

open scoped Classical in
private theorem forest_card_with_vertex {V : Type} [Fintype V] [Nonempty V]
    (F : SimpleGraph V) (hF : F.IsAcyclic) : F.edgeFinset.card + 1 ≤ Fintype.card V := by
  obtain ⟨T, hFT, _, hT⟩ :=
    (connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic (le_top : F ≤ ⊤) hF
  have hcard : F.edgeFinset.card ≤ T.edgeFinset.card :=
    Finset.card_le_card (edgeFinset_mono hFT)
  have hTreeCard := hT.card_edgeFinset
  omega

private lemma degree_eq_ncard_neighborSet {V : Type} (G : SimpleGraph V) (x : V)
    [Fintype (G.neighborSet x)] : G.degree x = (G.neighborSet x).ncard :=
  (Set.ncard_eq_toFinset_card' _).symm

open scoped Classical in
private lemma cycle_spanning_even {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v : V} (p : G.Walk v v)
    (hp : p.IsCycle) (x : V) : Even (p.toSubgraph.spanningCoe.degree x) := by
  let C : SimpleGraph V := p.toSubgraph.spanningCoe
  have hEdges : C.edgeFinset = p.edges.toFinset := by
    ext e
    simp only [C, mem_edgeFinset, Subgraph.edgeSet_spanningCoe,
      Walk.mem_edges_toSubgraph, List.mem_toFinset]
  have hParity := (hp.isTrail.even_countP_edges_iff x).2 (fun h => (h rfl).elim)
  change Even (C.degree x)
  rw [← C.card_incidenceFinset_eq_degree, C.incidenceFinset_eq_filter, hEdges]
  rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter] at hParity
  change Even (Multiset.filter (fun e => x ∈ e) (p.edges.toFinset.val)).card
  rwa [List.toFinset_val, List.dedup_eq_self.mpr hp.edges_nodup]

open scoped Classical in
theorem exists_even_with_acyclic_sdiff {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    ∃ E ≤ G, (∀ x, Even ((E.neighborSet x).ncard)) ∧ (G \ E).IsAcyclic := by
  let candidates := (Finset.univ : Finset (SimpleGraph V)).filter
    (fun E => E ≤ G ∧ ∀ x, Even (E.degree x))
  have hcandidates : candidates.Nonempty := ⟨⊥, by simp [candidates]⟩
  obtain ⟨E, hE, maximal⟩ := Finset.exists_max_image candidates
    (fun K => K.edgeSet.ncard) hcandidates
  obtain ⟨hEG, hEeven⟩ : E ≤ G ∧ ∀ x, Even (E.degree x) := (Finset.mem_filter.mp hE).2
  refine ⟨E, hEG, fun x => degree_eq_ncard_neighborSet E x ▸ hEeven x, ?_⟩
  intro v p hp
  let C : SimpleGraph V := p.toSubgraph.spanningCoe
  have hC : C ≤ G \ E := p.toSubgraph.spanningCoe_le
  have hDisj : Disjoint E C := disjoint_sdiff_self_right.mono_right hC
  have hSup : E ⊔ C ∈ candidates := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, sup_le hEG (hC.trans sdiff_le), ?_⟩
    intro x
    rw [degree_eq_ncard_neighborSet, neighborSet_sup,
      Set.ncard_union_eq (disjoint_neighborSet.mpr hDisj x)]
    simpa only [degree_eq_ncard_neighborSet] using
      (hEeven x).add (cycle_spanning_even p hp x)
  have hCne : C ≠ ⊥ := by
    have hl : p.edges ≠ [] := fun he => hp.not_nil (Walk.edges_eq_nil.mp he)
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p.edges hl
    have he' : e ∈ C.edgeSet := by
      simp only [C, Subgraph.edgeSet_spanningCoe, Walk.mem_edges_toSubgraph, he]
    intro hz
    simp [hz] at he'
  have hStrict : E < E ⊔ C := by
    apply lt_of_le_of_ne le_sup_left
    intro he
    have hCE : C ≤ E := he ▸ le_sup_right
    exact hCne (disjoint_self.mp (hDisj.mono_left hCE))
  exact (not_lt_of_ge (maximal _ hSup))
    (Set.ncard_lt_ncard (edgeSet_ssubset_edgeSet.mpr hStrict) (Set.toFinite _))

theorem main : H1 → H2 → OMA.R_Erdos184_erdos_184_variants_covering_R1.H2 := by
  intro hFan hCompress V _ _ G _
  apply of_connected _ V G
  intro V _ _ G hconn
  classical
  obtain ⟨E, hEG, hEeven, hforest⟩ := exists_even_with_acyclic_sdiff G
  let F := G \ E
  have hFcard : Fintype.card F.edgeSet + 1 ≤ Fintype.card V := by
    rw [← Nat.card_eq_fintype_card]
    have hcard := @forest_card_with_vertex V _ hconn.nonempty F hforest
    simpa only [edgeFinset_card, ← Nat.card_eq_fintype_card] using hcard
  obtain ⟨A, hOld, hCross, hNew⟩ := exists_augmentation G F
  obtain ⟨S, hS, hcover, hcard⟩ := hFan (V ⊕ F.edgeSet) A
    (augment_connected hOld hCross hconn) (augment_even hOld hCross hNew hEG hEeven rfl)
  obtain ⟨T, hT, hTcover, hTcard⟩ :=
    cover_of_augment hOld hCross hNew hCompress (show F ≤ G from sdiff_le) S hS hcover
  refine ⟨T, hT, hTcover, ?_⟩
  rw [Fintype.card_sum] at hcard
  omega

end OMA.R_Erdos184_erdos_184_variants_covering_R1_H2_R1
