import FormalConjectures.Wikipedia.BergeFulkersonConjecture

/-! Use the odd cuts of a bridgeless cubic graph to verify the Tutte condition. -/

open SimpleGraph
open scoped Classical

def OMA.petersen_edges_between {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Finset (V × V) :=
  (A ×ˢ B).filter fun p => G.Adj p.1 p.2

lemma OMA.petersen_edges_mem {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (p : V × V) :
    p ∈ OMA.petersen_edges_between G A B ↔ p.1 ∈ A ∧ p.2 ∈ B ∧ G.Adj p.1 p.2 := by
  simp [OMA.petersen_edges_between, Finset.mem_product, and_assoc]

lemma OMA.petersen_edges_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (OMA.petersen_edges_between G A B).card = ∑ x ∈ A, (G.neighborFinset x ∩ B).card := by
  classical
  have hproj : (↑(OMA.petersen_edges_between G A B) : Set (V × V)).MapsTo Prod.fst ↑A :=
    fun p hp => ((OMA.petersen_edges_mem G A B p).mp hp).1
  rw [Finset.card_eq_sum_card_fiberwise hproj]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.card_nbij' Prod.snd (fun y => (x, y))
  · intro p hp
    obtain ⟨hmem, heq⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hb, hadj⟩ := (OMA.petersen_edges_mem G A B p).mp hmem
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset x p.2).mpr (heq ▸ hadj), hb⟩
  · intro y hy
    obtain ⟨hn, hb⟩ := Finset.mem_inter.mp hy
    exact Finset.mem_filter.mpr
      ⟨(OMA.petersen_edges_mem G A B (x, y)).mpr ⟨hx, hb, (G.mem_neighborFinset x y).mp hn⟩, rfl⟩
  · intro p hp
    exact Prod.ext ((Finset.mem_filter.mp hp).2.symm) rfl
  · intro y _
    rfl

lemma OMA.petersen_edges_swap {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    (OMA.petersen_edges_between G A B).card = (OMA.petersen_edges_between G B A).card := by
  apply Finset.card_equiv (Equiv.prodComm V V)
  intro p
  rw [OMA.petersen_edges_mem, OMA.petersen_edges_mem]
  change (p.1 ∈ A ∧ p.2 ∈ B ∧ G.Adj p.1 p.2) ↔
      (p.2 ∈ B ∧ p.1 ∈ A ∧ G.Adj p.2 p.1)
  rw [G.adj_comm p.2 p.1]
  tauto

noncomputable def OMA.petersen_cut {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Set V) : Finset (V × V) :=
  OMA.petersen_edges_between G A.toFinset Aᶜ.toFinset

lemma OMA.petersen_cut_mem {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Set V) (p : V × V) :
    p ∈ OMA.petersen_cut G A ↔ p.1 ∈ A ∧ p.2 ∉ A ∧ G.Adj p.1 p.2 := by
  rw [OMA.petersen_cut, OMA.petersen_edges_mem]
  simp

lemma OMA.petersen_cut_balance {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : BergeFulkersonConjecture.IsCubic G)
    (A : Set V) :
    3 * A.ncard = 2 * (G.induce A).edgeFinset.card +
      (OMA.petersen_cut G A).card := by
  classical
  let inside (v : V) := (G.neighborFinset v ∩ A.toFinset).card
  let outside (v : V) := (G.neighborFinset v ∩ Aᶜ.toFinset).card
  have hsplit (v : V) : inside v + outside v = G.degree v := by
    have hI : G.neighborFinset v ∩ A.toFinset = (G.neighborFinset v).filter (· ∈ A) := by
      ext w
      simp
    have hO : G.neighborFinset v ∩ Aᶜ.toFinset = (G.neighborFinset v).filter (· ∉ A) := by
      ext w
      simp
    dsimp [inside, outside]
    rw [hI, hO, Finset.card_filter_add_card_filter_not, G.card_neighborFinset_eq_degree]
  have hinside (v : A) : inside v = (G.induce A).degree v := by
    calc
      inside v = (((G.induce A).neighborFinset v).map
          (Function.Embedding.subtype (· ∈ A))).card :=
        congrArg Finset.card (G.map_neighborFinset_induce v).symm
      _ = _ := by rw [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree]
  have hInSum : (∑ v ∈ A.toFinset, inside v) = 2 * (G.induce A).edgeFinset.card := by
    rw [← Finset.sum_set_coe A]
    calc
      (∑ v : A, inside v) = ∑ v : A, (G.induce A).degree v :=
        Finset.sum_congr rfl (fun v _ => hinside v)
      _ = _ := (G.induce A).sum_degrees_eq_twice_card_edges
  calc
    3 * A.ncard = ∑ v ∈ A.toFinset, G.degree v := by
      rw [Set.ncard_eq_toFinset_card' A]
      simp [show ∀ v : V, G.degree v = 3 from hcubic, Nat.mul_comm]
    _ = ∑ v ∈ A.toFinset, (inside v + outside v) :=
      Finset.sum_congr rfl (fun v _ => (hsplit v).symm)
    _ = _ := by
      rw [Finset.sum_add_distrib, hInSum, OMA.petersen_cut, OMA.petersen_edges_count]

lemma OMA.petersen_cut_not_singleton {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hbridge : G.IsBridgeless) (A : Set V) :
    (OMA.petersen_cut G A).card ≠ 1 := by
  classical
  intro hcard
  obtain ⟨⟨x, y⟩, hsingle⟩ := Finset.card_eq_one.mp hcard
  have hxy : (x, y) ∈ OMA.petersen_cut G A := by rw [hsingle]; simp
  obtain ⟨hxA, hyA, ha⟩ := (OMA.petersen_cut_mem G A (x, y)).mp hxy
  apply hbridge s(x, y) (show s(x, y) ∈ G.edgeSet from ha)
  rw [SimpleGraph.isBridge_iff]
  intro hReach
  let D := G.deleteEdges ({s(x, y)} : Set (Sym2 V))
  have hclosed {a b : V} (hA : a ∈ A) (hab : D.Adj a b) : b ∈ A := by
    by_contra hB
    obtain ⟨habG, hne⟩ := SimpleGraph.deleteEdges_adj.mp hab
    have habCut := (OMA.petersen_cut_mem G A (a, b)).mpr ⟨hA, hB, habG⟩
    rw [hsingle] at habCut
    have heq : (a, b) = (x, y) := Finset.mem_singleton.mp habCut
    exact hne (by rw [(Prod.mk.inj heq).1, (Prod.mk.inj heq).2]; simp)
  have hwalk {a b : V} (p : D.Walk a b) : a ∈ A → b ∈ A := by
    induction p with
    | nil => exact id
    | cons hadj _ ih => exact fun ha => ih (hclosed ha hadj)
  obtain ⟨p⟩ := hReach
  exact hyA (hwalk p hxA)

lemma OMA.petersen_cut_min {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : BergeFulkersonConjecture.IsCubic G)
    (hbridge : G.IsBridgeless) (A : Set V) (hOdd : Odd A.ncard) :
    3 ≤ (OMA.petersen_cut G A).card := by
  obtain ⟨a, ha⟩ := hOdd
  have hbalance := OMA.petersen_cut_balance G hcubic A
  have hsingle := OMA.petersen_cut_not_singleton G hbridge A
  omega

set_option maxHeartbeats 1000000 in
theorem OMA.solution : type_of% @BergeFulkersonConjecture.berge_fulkerson_conjecture.variants.petersen := by
  intro V _ _ G _ hcubic hbridge
  classical
  apply (SimpleGraph.tutte (G := G)).mpr
  intro U
  let D := (⊤ : G.Subgraph).deleteVerts U
  let C := D.coe
  let part (c : C.ConnectedComponent) : Set V := Subtype.val '' c.supp
  let odd := C.oddComponents.toFinset
  let cut (c : C.ConnectedComponent) := OMA.petersen_cut G (part c)
  have hOutside (x : V) : x ∈ D.verts ↔ x ∉ U := by simp [D]
  have hclosed (c : C.ConnectedComponent) {x y : V} (hx : x ∈ part c) (hy : y ∉ U)
      (hAdj : G.Adj x y) : y ∈ part c := by
    have hxd : x ∈ D.verts := by
      obtain ⟨x', _, rfl⟩ := hx
      exact x'.property
    have hAdjD : D.Adj x y := Subgraph.deleteVerts_adj.mpr
      ⟨by simp, (hOutside x).mp hxd, by simp, hy, hAdj⟩
    exact ConnectedComponent.mem_coe_supp_of_adj hx ((hOutside y).mpr hy) hAdjD
  have hcut (c : C.ConnectedComponent) (hc : c ∈ odd) : 3 ≤ (cut c).card := by
    have hOdd : Odd c.supp.ncard := (Set.mem_toFinset (s := C.oddComponents) (a := c)).mp hc
    have hpartCard : (part c).ncard = c.supp.ncard :=
      Set.ncard_image_of_injective _ Subtype.val_injective
    have hOddPart : Odd (part c).ncard := by rwa [hpartCard]
    exact OMA.petersen_cut_min G hcubic hbridge (part c) hOddPart
  have hdisjoint : (odd : Set C.ConnectedComponent).PairwiseDisjoint cut := by
    intro c _ c' _ hne
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    have hx : p.1 ∈ part c :=
      ((OMA.petersen_cut_mem G (part c) p).mp hp).1
    have hx' : p.1 ∈ part c' :=
      ((OMA.petersen_cut_mem G (part c') p).mp hp').1
    obtain ⟨a, ha, heq⟩ := hx
    obtain ⟨b, hb, hbeq⟩ := hx'
    have hab : a = b := Subtype.val_injective (heq.trans hbeq.symm)
    subst b
    exact hne (ConnectedComponent.eq_of_common_vertex ha hb)
  have hsub : odd.biUnion cut ⊆ OMA.petersen_edges_between G Finset.univ U.toFinset := by
    intro p hp
    obtain ⟨c, _, hpc⟩ := Finset.mem_biUnion.mp hp
    have hmem := (OMA.petersen_cut_mem G (part c) p).mp hpc
    have hx : p.1 ∈ part c := hmem.1
    have hy : p.2 ∉ part c := hmem.2.1
    have hyU : p.2 ∈ U := by
      by_contra h
      exact hy (hclosed c hx h hmem.2.2)
    exact (OMA.petersen_edges_mem G _ _ p).mpr
      ⟨Finset.mem_univ _, Set.mem_toFinset.mpr hyU, hmem.2.2⟩
  have hUpper : (OMA.petersen_edges_between G Finset.univ U.toFinset).card = 3 * U.ncard := by
    rw [OMA.petersen_edges_swap, OMA.petersen_edges_count]
    rw [Set.ncard_eq_toFinset_card' U]
    simp [show ∀ v : V, G.degree v = 3 from hcubic, Nat.mul_comm]
  have hLo : 3 * odd.card ≤ (odd.biUnion cut).card := by
    rw [Finset.card_biUnion hdisjoint]
    calc
      3 * odd.card = ∑ _ ∈ odd, (3 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hcut
  have hTotal := hLo.trans (Finset.card_le_card hsub)
  rw [hUpper] at hTotal
  show ¬ U.ncard < C.oddComponents.ncard
  have hOddCard : C.oddComponents.ncard = odd.card := Set.ncard_eq_toFinset_card' C.oddComponents
  rw [hOddCard]
  omega