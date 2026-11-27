import FormalConjectures.ErdosProblems.«64»
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
Reduce the Erdős–Gyárfás conjecture to two classes distinguished by triangles.
First minimize the number of vertices, and then edges. High-degree vertices are
independent, and every vertex has a cubic neighbor (Markström, 2004 and Carr,
arXiv:2605.22844). Deleting a set closed under cubic neighbors forces a vertex
outside the set to have all but at most two neighbors inside it.

In the triangle-free case this rules out cubic components of order below four.
Counting cross edges then makes at least eight elevenths of all vertices cubic.
With a triangle, the bound is two thirds. In this case a cycle with a private
triangular detour at each edge already yields all lengths from m through 2m.
The remaining graph classes are stated in the two hypotheses below.
-/

-- Credit: @zarnab222-dev

section

open SimpleGraph Finset
open scoped Classical

namespace E64Critical

private theorem same_minimum {W : Type*} (J : SimpleGraph W) (f g : Fintype W)
    (d e : DecidableRel J.Adj) :
    @SimpleGraph.minDegree W J f d = @SimpleGraph.minDegree W J g e := by
  cases Subsingleton.elim f g
  cases Subsingleton.elim d e
  rfl

private theorem classical_minimum {V : Type*} [Fintype V] (G : SimpleGraph V)
    [d : DecidableRel G.Adj] (h : 3 ≤ G.minDegree) :
    (letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _; 3 ≤ G.minDegree) := by
  have hd : d = (fun _ _ => Classical.propDecidable _) := Subsingleton.elim _ _
  cases hd
  exact h

private theorem numbered {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (minimum : 3 ≤ G.minDegree)
    (bad : ¬ ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k) :
    ∃ H : SimpleGraph (Fin (Fintype.card V)), 3 ≤ H.minDegree ∧
      ¬ ∃ (k : ℕ) (v : Fin (Fintype.card V)) (c : H.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
  let e := (Fintype.equivFin V).symm
  let H := G.comap e
  let iso : H ≃g G := SimpleGraph.Iso.comap e G
  refine ⟨H,?_,?_⟩
  · exact classical_minimum H (minimum.trans iso.minDegree_eq.ge)
  · rintro ⟨k,v,c,hk,hc,hl⟩
    exact bad ⟨k,iso v,c.map iso.toHom,hk,hc.map iso.injective,by simpa using hl⟩

private theorem delete_high_edge {n : ℕ} (G : SimpleGraph (Fin n)) {a b : Fin n}
    (minimum : 3 ≤ G.minDegree) (adj : G.Adj a b)
    (ha : 4 ≤ G.degree a) (hb : 4 ≤ G.degree b) :
    3 ≤ (G.deleteEdges {s(a,b)}).minDegree := by
  let H := G.deleteEdges {s(a,b)}
  have : Nonempty (Fin n) := ⟨a⟩
  apply H.le_minDegree_of_forall_le_degree
  intro v
  have changeRow : H.neighborFinset v =
      if v = a then (G.neighborFinset v).erase b else
      if v = b then (G.neighborFinset v).erase a else G.neighborFinset v := by
    ext z
    split_ifs <;> simp only [H,mem_neighborFinset,deleteEdges_adj,Set.mem_singleton_iff,
      Sym2.eq_iff,mem_erase] <;> grind
  change 3 ≤ (H.neighborFinset v).card
  rw [changeRow]
  split_ifs with va vb
  · subst v
    rw [card_erase_of_mem ((G.mem_neighborFinset a b).mpr adj),card_neighborFinset_eq_degree]
    omega
  · subst v
    rw [card_erase_of_mem ((G.mem_neighborFinset b a).mpr adj.symm),card_neighborFinset_eq_degree]
    omega
  · exact minimum.trans (G.minDegree_le_degree v)

theorem critical {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (minimum : 3 ≤ G.minDegree)
    (bad : ¬ ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k) :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)), 3 ≤ H.minDegree ∧
      (¬ ∃ (k : ℕ) (v : Fin n) (c : H.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k) ∧
      (∀ S : Set (Fin n), S.Nonempty → S ≠ Set.univ → (H.induce S).minDegree < 3) ∧
      (∀ ⦃a b⦄, H.Adj a b → H.degree a = 3 ∨ H.degree b = 3) ∧
      (∀ a, ∃ b, H.Adj a b ∧ H.degree b = 3) := by
  let P {n : ℕ} (H : SimpleGraph (Fin n)) := 3 ≤ H.minDegree ∧
    ¬ ∃ (k : ℕ) (v : Fin n) (c : H.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k
  have someOrder : ∃ n, ∃ H : SimpleGraph (Fin n), P H :=
    ⟨Fintype.card V,numbered G minimum bad⟩
  let n := Nat.find someOrder
  obtain ⟨J,hJ⟩ : ∃ J : SimpleGraph (Fin n), P J := Nat.find_spec someOrder
  have someSize : ∃ m, ∃ H : SimpleGraph (Fin n), P H ∧ H.edgeFinset.card = m :=
    ⟨_,J,hJ,rfl⟩
  obtain ⟨H,⟨hmin,noCycle⟩,edgeCount⟩ := Nat.find_spec someSize
  have proper (S : Set (Fin n)) (_ : S.Nonempty) (hne : S ≠ Set.univ) :
      (H.induce S).minDegree < 3 := by
    by_contra! h
    obtain ⟨v,hv⟩ := (Set.ne_univ_iff_exists_notMem S).mp hne
    have less : Fintype.card S < n := by
      simpa using Fintype.card_lt_of_injective_of_notMem (fun y : S => y.val) Subtype.val_injective
        (b := v) (fun ⟨y,eq⟩ => hv (eq ▸ y.property))
    have badS : ¬ ∃ (k : ℕ) (v : S) (c : (H.induce S).Walk v v),
        2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
      rintro ⟨k,u,c,hk,hc,hl⟩
      let lift : H.induce S →g H := ⟨Subtype.val,fun hh => hh⟩
      exact noCycle ⟨k,u.val,c.map lift,hk,hc.map Subtype.val_injective,by simpa using hl⟩
    exact Nat.find_min someOrder less (numbered (H.induce S) h badS)
  refine ⟨n,H,hmin,noCycle,proper,?_,?_⟩
  · intro a b adj
    by_contra! h
    have ha := hmin.trans (H.minDegree_le_degree a)
    have hb := hmin.trans (H.minDegree_le_degree b)
    let K := H.deleteEdges {s(a,b)}
    have small : K.edgeFinset.card < Nat.find someSize := by
      have erased : K.edgeFinset = H.edgeFinset.erase s(a,b) := by
        ext e
        simp [K,edgeSet_deleteEdges,and_comm]
      rw [erased,← edgeCount]
      exact card_erase_lt_of_mem (H.mem_edgeFinset.mpr adj)
    have ma : 4 ≤ H.degree a := by omega
    have mb : 4 ≤ H.degree b := by omega
    have minK := classical_minimum K (delete_high_edge H hmin adj ma mb)
    apply Nat.find_min someSize small
    refine ⟨K,⟨minK,?_⟩,?_⟩
    · rintro ⟨k,v,c,hk,hc,hl⟩
      have leH : K ≤ H := H.deleteEdges_le _
      exact noCycle ⟨k,v,c.mapLe leH,hk,hc.mapLe leH,by simpa using hl⟩
    · apply congrArg Finset.card
      ext e
      simp only [SimpleGraph.mem_edgeFinset]
  · intro a
    let S : Set (Fin n) := {v | v ≠ a}
    have lower := hmin.trans (H.minDegree_le_degree a)
    obtain ⟨b,hb⟩ := (H.degree_pos_iff_exists_adj a).mp (by omega)
    have sn : S.Nonempty := ⟨b,hb.ne.symm⟩
    have : Nonempty S := sn.to_subtype
    have small := proper S sn (by
      intro heq
      have ha : a ∈ S := heq ▸ Set.mem_univ a
      exact ha rfl)
    obtain ⟨v,hv⟩ := (H.induce S).exists_minimal_degree_vertex
    have smallDegree : (H.induce S).degree v < 3 :=
      lt_of_eq_of_lt (hv.symm.trans (same_minimum _ _ _ _ _)) small
    have changed : ((H.induce S).neighborFinset v).map (.subtype (· ∈ S)) =
        (H.neighborFinset v.val).erase a := by
      rw [SimpleGraph.map_neighborFinset_induce]
      ext z
      simp [S,and_comm]
    have count := congrArg Finset.card changed
    rw [card_map,card_neighborFinset_eq_degree] at count
    have general := hmin.trans (H.minDegree_le_degree v.val)
    by_cases ha : a ∈ H.neighborFinset v.val
    · rw [card_erase_of_mem ha,card_neighborFinset_eq_degree] at count
      exact ⟨v.val,((H.mem_neighborFinset v.val a).mp ha).symm,by omega⟩
    · rw [erase_eq_of_notMem ha,card_neighborFinset_eq_degree] at count
      omega

end E64Critical

end

section

open SimpleGraph Finset
open scoped Classical

namespace E64Minimal

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A vertex of minimum degree in the complement witnesses the concentration
of neighbors in the cut. Cubic-neighbor closure puts its degree above three. -/
theorem cut_witness (minimum : 3 ≤ G.minDegree) (C : Finset V)
    (outside : ∃ v, v ∉ C)
    (closed : ∀ ⦃u v⦄, u ∈ C → G.Adj u v → G.degree v = 3 → v ∈ C)
    (low : (G.induce {v | v ∉ C}).minDegree < 3) :
    ∃ v ∉ C, 4 ≤ G.degree v ∧ G.degree v - 2 ≤ ((G.neighborFinset v) ∩ C).card := by
  let S : Set V := {v | v ∉ C}
  obtain ⟨b,hb⟩ := outside
  have : Nonempty S := ⟨⟨b,hb⟩⟩
  obtain ⟨v,hv⟩ := (G.induce S).exists_minimal_degree_vertex
  have small : (G.induce S).degree v < 3 := hv ▸ low
  have remaining : ((G.induce S).neighborFinset v).map (.subtype (· ∈ S)) =
      (G.neighborFinset v.val) \ C := by
    rw [SimpleGraph.map_neighborFinset_induce]
    ext u
    simp [S]
  have counts := congrArg Finset.card remaining
  rw [card_map,card_neighborFinset_eq_degree] at counts
  have split := card_sdiff_add_card_inter (G.neighborFinset v.val) C
  rw [card_neighborFinset_eq_degree] at split
  have lower := minimum.trans (G.minDegree_le_degree v.val)
  have positive : 0 < ((G.neighborFinset v.val) ∩ C).card := by omega
  obtain ⟨u,hu⟩ := card_pos.mp positive
  have adj := (G.mem_neighborFinset v.val u).mp (mem_inter.mp hu).1
  have notThree : G.degree v.val ≠ 3 := fun h => v.property (closed (mem_inter.mp hu).2 adj.symm h)
  exact ⟨v.val,v.property,by omega,by omega⟩

end E64Minimal

end

section

open Finset SimpleGraph

namespace CubicCount

private theorem two_thirds {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : 3 ≤ G.minDegree)
    (edge : ∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3)
    (nbr : ∀ a, ∃ b, G.Adj a b ∧ G.degree b = 3) :
    2 * Fintype.card V ≤ 3 * (univ.filter (fun x => G.degree x = 3)).card := by
  classical
  let L := univ.filter fun x => G.degree x = 3
  let H := univ.filter fun x => G.degree x ≠ 3
  let cross (x : V) := (G.neighborFinset x).filter (· ∈ H)
  have sums :
      (∑ x ∈ H, G.degree x) = ∑ y ∈ L, (cross y).card := by
    calc
      _ = ∑ x ∈ H, ∑ y ∈ L, if G.Adj x y then 1 else 0 := by
        apply sum_congr rfl
        intro x hx
        have hn : G.degree x ≠ 3 := (mem_filter.mp hx).2
        have same : L.filter (G.Adj x) = G.neighborFinset x := by
          ext y
          simp only [L,mem_filter,mem_univ,true_and, G.mem_neighborFinset]
          exact ⟨And.right, fun h => ⟨(edge h).resolve_left hn,h⟩⟩
        rw [← sum_filter (G.Adj x) (fun _ => 1),same,sum_const,smul_eq_mul,mul_one,
          G.card_neighborFinset_eq_degree]
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro y hy
        have same : H.filter (fun x => G.Adj x y) = cross y := by
          ext x
          simp [cross,G.adj_comm,and_comm]
        rw [← sum_filter (fun x => G.Adj x y) (fun _ => 1),same,sum_const,smul_eq_mul,mul_one]
  have lower : 4 * H.card ≤ ∑ x ∈ H, G.degree x := by
    calc
      _ = ∑ _x ∈ H, 4 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (by
        intro x hx
        have := hmin.trans (G.minDegree_le_degree x)
        have hh := (mem_filter.mp hx).2
        omega)
  have upper : ∑ y ∈ L, (cross y).card ≤ 2*L.card := by
    calc
      _ ≤ ∑ _y ∈ L, 2 := sum_le_sum (by
        intro y hy
        obtain ⟨t,ht,hdt⟩ := nbr y
        have hc : cross y ⊆ (G.neighborFinset y).erase t := by
          intro x hx
          obtain ⟨hyx,hxH⟩ := mem_filter.mp hx
          exact mem_erase.mpr ⟨fun he => (mem_filter.mp hxH).2 (he ▸ hdt),hyx⟩
        have hb := card_le_card hc
        rw [card_erase_of_mem ((G.mem_neighborFinset ..).mpr ht),
          G.card_neighborFinset_eq_degree,(mem_filter.mp hy).2] at hb
        exact hb)
      _ = _ := by simp [mul_comm]
  have parts := (univ : Finset V).card_filter_add_card_filter_not (fun x => G.degree x = 3)
  change L.card + H.card = (univ : Finset V).card at parts
  rw [card_univ] at parts
  change 2 * Fintype.card V ≤ 3 * L.card
  omega

end CubicCount

end

section

open SimpleGraph Finset
open scoped Classical

namespace CubicGirth

private theorem square {V : Type*} {G : SimpleGraph V} {v a u b : V}
    (va : G.Adj v a) (au : G.Adj a u) (ub : G.Adj u b) (bv : G.Adj b v)
    (hab : a ≠ b) (huv : u ≠ v) :
    ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
  let c := Walk.cons va (Walk.cons au (Walk.cons ub (Walk.cons bv Walk.nil)))
  refine ⟨2,v,c,by decide,?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · simp [c,Walk.isPath_def,hab,huv,va.ne.symm,au.ne,ub.ne,bv.ne]
  · change 3 ≤ 4
    decide

private theorem common_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (bad : ¬∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (x y : V) (hxy : x ≠ y) :
    ((G.neighborFinset x) ∩ G.neighborFinset y).card ≤ 1 := by
  by_contra! many
  obtain ⟨a,b,ha,hb,hab⟩ := one_lt_card_iff.mp many
  obtain ⟨hxa,hya⟩ := mem_inter.mp ha
  obtain ⟨hxb,hyb⟩ := mem_inter.mp hb
  exact bad (square ((G.mem_neighborFinset ..).mp hxa) ((G.mem_neighborFinset ..).mp hya).symm
    ((G.mem_neighborFinset ..).mp hyb) ((G.mem_neighborFinset ..).mp hxb).symm hab hxy.symm)

private theorem component_size {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (nbr : ∀ a, ∃ b, G.Adj a b ∧ G.degree b = 3)
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (bad : ¬∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (cut : ∀ C : Finset V, C.Nonempty → (∃ v, v ∉ C) →
      (∀ ⦃x y⦄, x ∈ C → G.Adj x y → G.degree y = 3 → y ∈ C) →
      ∃ v ∉ C, 4 ≤ G.degree v ∧ G.degree v - 2 ≤ ((G.neighborFinset v) ∩ C).card)
    (K : (G.induce {v | G.degree v = 3}).ConnectedComponent) :
    4 ≤ K.supp.ncard := by
  classical
  let L : Set V := {v | G.degree v = 3}
  let C : Finset V := K.supp.toFinset.map (.subtype (· ∈ L))
  have mem (x : V) : x ∈ C ↔ ∃ h : x ∈ L, (⟨x,h⟩ : L) ∈ K.supp := by
    simp [C,Finset.mem_map]
  have size : C.card = K.supp.ncard := by
    simp only [C,card_map,Set.toFinset_card,Set.fintypeCard_eq_ncard]
  have cc : C.Nonempty := by
    obtain ⟨x,hx⟩ := K.nonempty_supp
    exact ⟨x.val,(mem _).mpr ⟨x.property,hx⟩⟩
  have closed : ∀ ⦃x y⦄, x ∈ C → G.Adj x y → G.degree y = 3 → y ∈ C := by
    intro x y hx ha hy
    obtain ⟨hxl,hxk⟩ := (mem _).mp hx
    have localEdge : (G.induce L).Adj (⟨x,hxl⟩ : L) ⟨y,hy⟩ := ha
    exact (mem _).mpr ⟨hy, (K.mem_supp_congr_adj localEdge).mp hxk⟩
  rw [← size]
  by_cases hAll : ∀ x, x ∈ C
  · have he : C = univ := eq_univ_iff_forall.mpr hAll
    obtain ⟨x,hx⟩ := cc
    obtain ⟨hg,_⟩ := (mem _).mp hx
    change G.degree x = 3 at hg
    rw [he,card_univ]
    have := G.degree_lt_card_verts x
    omega
  push Not at hAll
  obtain ⟨v,hvC,hv,hcut⟩ := cut C cc hAll closed
  obtain ⟨a,b,ha,hb,hab⟩ := one_lt_card_iff.mp
    (show 1 < ((G.neighborFinset v) ∩ C).card by omega)
  obtain ⟨hva,haC⟩ := mem_inter.mp ha
  obtain ⟨hvb,hbC⟩ := mem_inter.mp hb
  have va := (G.mem_neighborFinset ..).mp hva
  have vb := (G.mem_neighborFinset ..).mp hvb
  have ab : ¬G.Adj a b := fun h => tri _ _ _ va h vb.symm
  obtain ⟨u,au,hu⟩ := nbr a
  obtain ⟨w,bw,hw⟩ := nbr b
  have huC := closed haC au hu
  have hwC := closed hbC bw hw
  have aus : a ≠ u := au.ne
  have bws : b ≠ w := bw.ne
  have ubs : u ≠ b := fun e => ab (e ▸ au)
  have was : w ≠ a := fun e => ab (e ▸ bw.symm)
  have uw : u ≠ w := by
    rintro rfl
    exact bad (square va au bw.symm vb.symm hab (fun h => hvC (h ▸ huC)))
  have sub : ({a,b,u,w} : Finset V) ⊆ C := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl|rfl|rfl <;> assumption
  have bound := card_le_card sub
  simpa [hab,aus,was.symm,bws,ubs.symm,uw] using bound

end CubicGirth

end

section

open Finset SimpleGraph

namespace CubicCount

private theorem density_from_components {W : Type*} [Fintype W] (Q : SimpleGraph W)
    [DecidableRel Q.Adj] (size : ∀ C : Q.ConnectedComponent, 4 ≤ C.supp.ncard) :
    3 * Fintype.card W ≤ 2 * ∑ x, Q.degree x := by
  classical
  have byComponent (f : W → ℕ) :
      (∑ C : Q.ConnectedComponent, ∑ x : C, f x) = ∑ x : W, f x := by
    rw [← Fintype.sum_sigma' (fun (C : Q.ConnectedComponent) (x : C) => f x)]
    let e : (Σ C : Q.ConnectedComponent, C) ≃ W := Equiv.sigmaFiberEquiv Q.connectedComponentMk
    exact Fintype.sum_equiv e _ _ fun _ => rfl
  have localBound (C : Q.ConnectedComponent) :
      3 * Fintype.card C ≤ 2 * ∑ x : C, Q.degree x := by
    have hcard : 4 ≤ Fintype.card C := by
      rw [← Nat.card_eq_fintype_card]
      exact size C
    have hconn := C.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← C.toSimpleGraph.edgeFinset_card] at hconn
    have hdeg := C.toSimpleGraph.sum_degrees_eq_twice_card_edges
    have preserve (x : C) : C.toSimpleGraph.degree x = Q.degree x := by
      convert! Q.degree_induce_of_neighborSet_subset (v := (⟨x, x.property⟩ : C.supp))
        (fun y hy => C.mem_supp_of_adj_mem_supp x.property hy) using 1
      congr 1
      exact Subsingleton.elim _ _
    simp only [preserve] at hdeg
    omega
  have hs := Finset.sum_le_sum (s := Finset.univ) fun C _ => localBound C
  have cards : (∑ C : Q.ConnectedComponent, Fintype.card C) = Fintype.card W := by
    simpa using byComponent (fun _ => 1)
  simpa only [← Finset.mul_sum, cards, byComponent (fun x => Q.degree x)] using hs

/-- If all degree-three components have at least four vertices, at least eight
elevenths of the full vertex set has degree three. -/
theorem eight_elevenths {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : 3 ≤ G.minDegree)
    (edge : ∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3)
    (size : ∀ C : (G.induce {x : V | G.degree x = 3}).ConnectedComponent,
      4 ≤ C.supp.ncard) :
    8 * Fintype.card V ≤ 11 * (univ.filter (fun x => G.degree x = 3)).card := by
  classical
  let L := univ.filter fun x => G.degree x = 3
  let _ : Fintype (↑L : Set V) := inferInstanceAs (Fintype ↥L)
  let H := univ.filter fun x => G.degree x ≠ 3
  let Q := G.induce (L : Set V)
  let inside (x : V) := (G.neighborFinset x).filter (· ∈ L)
  let cross (x : V) := (G.neighborFinset x).filter (· ∈ H)
  have hL : (L : Set V) = {x : V | G.degree x = 3} := by ext x; simp [L]
  have hsize : ∀ C : Q.ConnectedComponent, 4 ≤ C.supp.ncard := by
    dsimp only [Q]
    rw [hL]
    exact size
  have hdeg (v : L) : Q.degree v = (inside v).card := by
    have he := congrArg Finset.card (G.map_neighborFinset_induce (s := (L : Set V)) v)
    simp [Q, inside, Finset.filter_mem_eq_inter] at he ⊢
    convert! he using 1
    congr 1
    exact Subsingleton.elim _ _
  have internal : 3 * L.card ≤ 2 * ∑ v ∈ L, (inside v).card := by
    have he := density_from_components Q hsize
    change 3 * Fintype.card ↥L ≤ 2 * ∑ v : L, Q.degree v at he
    simpa only [Fintype.card_coe, hdeg, L.sum_coe_sort (fun v => (inside v).card)] using he
  have sums : (∑ x ∈ H, G.degree x) = ∑ y ∈ L, (cross y).card := by
    calc
      _ = ∑ x ∈ H, ∑ y ∈ L, if G.Adj x y then 1 else 0 := by
        apply sum_congr rfl
        intro x hx
        have hn : G.degree x ≠ 3 := (mem_filter.mp hx).2
        have same : L.filter (G.Adj x) = G.neighborFinset x := by
          ext y
          simp only [L, mem_filter, mem_univ, true_and, G.mem_neighborFinset]
          exact ⟨And.right, fun h => ⟨(edge h).resolve_left hn,h⟩⟩
        rw [Finset.sum_boole, same, G.card_neighborFinset_eq_degree]
        rfl
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro y hy
        have same : H.filter (fun x => G.Adj x y) = cross y := by
          ext x
          simp [cross,G.adj_comm,and_comm]
        rw [Finset.sum_boole, same]
        rfl
  have lower : 4 * H.card ≤ ∑ x ∈ H, G.degree x := by
    calc
      _ = ∑ _x ∈ H, 4 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (by
        intro x hx
        have := hmin.trans (G.minDegree_le_degree x)
        have hh := (mem_filter.mp hx).2
        omega)
  have total : (∑ y ∈ L, (inside y).card) + (∑ y ∈ L, (cross y).card) = 3*L.card := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _y ∈ L, 3 := by
        refine sum_congr rfl fun y hy => ?_
        have hd : G.degree y = 3 := (mem_filter.mp hy).2
        simpa only [L, H, inside, cross, mem_filter, mem_univ, true_and,
          G.card_neighborFinset_eq_degree, hd] using
          (G.neighborFinset y).card_filter_add_card_filter_not (fun z => G.degree z = 3)
      _ = _ := by simp [mul_comm]
  have parts := (univ : Finset V).card_filter_add_card_filter_not (fun x => G.degree x = 3)
  change L.card + H.card = (univ : Finset V).card at parts
  rw [card_univ] at parts
  change 8 * Fintype.card V ≤ 11 * L.card
  omega

end CubicCount

end

section

open SimpleGraph

namespace E64Ring

private theorem successor_val {n : ℕ} [NeZero n] (i : Fin n) :
    (i+1).val = if i.val+1<n then i.val+1 else 0 := by
  cases n with
  | zero => exact i.elim0
  | succ u =>
    rw [Fin.val_add_one]
    simp only [Fin.ext_iff,Fin.val_last]
    split <;> split <;> omega

private theorem cycle_of_successors {V : Type*} {G : SimpleGraph V} {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) (v : Fin n ↪ V) (adj : ∀ i, G.Adj (v i) (v (i+1))) :
    ∃ (x : V) (p : G.Walk x x), p.IsCycle ∧ p.length = n := by
  obtain ⟨u,rfl⟩ : ∃ u, n=u+2 := ⟨n-2,by omega⟩
  apply (cycleGraph_isContained_iff hn).mp
  refine ⟨⟨⟨v,?_⟩,v.injective⟩⟩
  intro a b h
  rcases cycleGraph_adj.mp h with h|h
  · have eq : a=b+1 := by simpa [add_comm] using (sub_eq_iff_eq_add.mp h)
    simpa only [eq] using (adj b).symm
  · have eq : b=a+1 := by simpa [add_comm] using (sub_eq_iff_eq_add.mp h)
    simpa only [eq] using adj a

private theorem triangle_ring_lengths {V : Type*} {G : SimpleGraph V} {m : ℕ} [NeZero m]
    (hm : 3 ≤ m) (v : Fin (2*m) ↪ V) (side : ∀ i, G.Adj (v i) (v (i+1)))
    (shortcut : ∀ i : Fin m, G.Adj (v ⟨2*i.val,by omega⟩)
      (v ⟨2*(i+1).val,by have := (i+1).isLt; omega⟩))
    {k : ℕ} (hk : k ≤ m) :
    ∃ (x : V) (p : G.Walk x x), p.IsCycle ∧ p.length = m+k := by
  let : NeZero (m+k) := ⟨by omega⟩
  let slot (j : Fin (m+k)) : Fin (2*m) :=
    ⟨if j.val < 2*k then j.val else 2*(j.val-k),by split <;> omega⟩
  have inj : Function.Injective slot := by
    intro a b eq
    apply Fin.ext
    have hv := congrArg Fin.val eq
    dsimp [slot] at hv
    split at hv <;> split at hv <;> omega
  let label := (⟨slot,inj⟩ : Fin (m+k) ↪ Fin (2*m)).trans v
  apply cycle_of_successors (by omega) label
  intro j
  change G.Adj (v (slot j)) (v (slot (j+1)))
  by_cases hj : j.val < 2*k
  · have eq : slot (j+1) = slot j + 1 := by
      apply Fin.ext
      simp only [slot,successor_val,hj,if_true]
      split_ifs <;> omega
    rw [eq]
    exact side _
  · let i : Fin m := ⟨j.val-k,by omega⟩
    have eq : slot j = ⟨2*i.val,by omega⟩ := by apply Fin.ext; simp [slot,i,hj]
    have nx : slot (j+1) = ⟨2*(i+1).val,by have := (i+1).isLt; omega⟩ := by
      apply Fin.ext
      simp only [slot,successor_val,i]
      split_ifs <;> omega
    rw [eq,nx]
    exact shortcut i

private theorem triangle_ring_power {V : Type*} {G : SimpleGraph V} {m : ℕ} [NeZero m]
    (hm : 3 ≤ m) (v : Fin (2*m) ↪ V) (side : ∀ i, G.Adj (v i) (v (i+1)))
    (shortcut : ∀ i : Fin m, G.Adj (v ⟨2*i.val,by omega⟩)
      (v ⟨2*(i+1).val,by have := (i+1).isLt; omega⟩)) :
    ∃ (k : ℕ) (x : V) (p : G.Walk x x), k ≥ 2 ∧ p.IsCycle ∧ p.length = 2^k := by
  let k := (Nat.log 2 m).succ
  have lo : m < 2^k := Nat.lt_pow_succ_log_self (by decide) m
  have hi : 2^k ≤ 2*m := by
    have h := Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
    dsimp [k]; rw [pow_succ]; omega
  have hk : 2 ≤ k := by
    by_contra! h
    interval_cases k <;> simp_all
    omega
  obtain ⟨x,p,hp,hlen⟩ := triangle_ring_lengths hm v side shortcut (show 2^k-m ≤ m by omega)
  exact ⟨k,x,p,hk,hp,by omega⟩

end E64Ring

end

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos64_erdos_64_R2

/-- Triangle-free case. Every cubic component has at least four vertices. -/
def H1 : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  3 ≤ G.minDegree →
  (∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3) →
  (∀ a, ∃ b, G.Adj a b ∧ G.degree b = 3) →
  (∀ a b, a ≠ b → ((G.neighborFinset a) ∩ G.neighborFinset b).card ≤ 1) →
  (∀ C : Finset (Fin n), C.Nonempty → (∃ x, x ∉ C) →
    (∀ ⦃a b⦄, a ∈ C → G.Adj a b → G.degree b = 3 → b ∈ C) →
    ∃ v ∉ C, 4 ≤ G.degree v ∧ G.degree v - 2 ≤ ((G.neighborFinset v) ∩ C).card) →
  (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
  (∀ C : (G.induce {x : Fin n | G.degree x = 3}).ConnectedComponent, 4 ≤ C.supp.ncard) →
  8*n ≤ 11*(univ.filter (fun x => G.degree x = 3)).card →
  ∃ (k : ℕ) (v : Fin n) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k

/-- Case with a triangle. There is no cycle with distinct private triangular detours along all edges. -/
def H2 : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  3 ≤ G.minDegree →
  (∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3) →
  (∀ a, ∃ b, G.Adj a b ∧ G.degree b = 3) →
  (∀ a b, a ≠ b → ((G.neighborFinset a) ∩ G.neighborFinset b).card ≤ 1) →
  (∀ C : Finset (Fin n), C.Nonempty → (∃ x, x ∉ C) →
    (∀ ⦃a b⦄, a ∈ C → G.Adj a b → G.degree b = 3 → b ∈ C) →
    ∃ v ∉ C, 4 ≤ G.degree v ∧ G.degree v - 2 ≤ ((G.neighborFinset v) ∩ C).card) →
  (∃ a b c, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) →
  (∀ (m : ℕ) [NeZero m], 3 ≤ m → ∀ e : Fin (2*m) ↪ Fin n,
    (∀ i, G.Adj (e i) (e (i+1))) →
    ¬ (∀ i : Fin m, G.Adj (e ⟨2*i.val,by omega⟩)
      (e ⟨2*(i+1).val,by have := (i+1).isLt; omega⟩))) →
  2*n ≤ 3*(univ.filter (fun x => G.degree x = 3)).card →
  ∃ (k : ℕ) (v : Fin n) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k

section

set_option maxHeartbeats 1000000 in
theorem main : H1 → H2 → type_of% @Erdos64.erdos_64 := by
  intro noTri hasTri V G instF instD minimum
  classical
  by_contra bad
  obtain ⟨n,H,hm,miss,critical,edge,nbr⟩ := E64Critical.critical G minimum bad
  have cut (C : Finset (Fin n)) (hC : C.Nonempty) (outside : ∃ x, x ∉ C)
      (closed : ∀ ⦃a b⦄, a ∈ C → H.Adj a b → H.degree b = 3 → b ∈ C) :
      ∃ v ∉ C, 4 ≤ H.degree v ∧ H.degree v - 2 ≤ ((H.neighborFinset v) ∩ C).card := by
    obtain ⟨x,hx⟩ := outside
    obtain ⟨y,hy⟩ := hC
    apply E64Minimal.cut_witness H hm C ⟨x,hx⟩ closed
    have proper : ({v | v ∉ C} : Set (Fin n)) ≠ Set.univ := by
      intro eq
      have hy' : y ∈ ({v | v ∉ C} : Set (Fin n)) := eq ▸ Set.mem_univ y
      exact hy' hy
    have low := critical ({v | v ∉ C} : Set (Fin n)) ⟨x,hx⟩ proper
    convert! low using 2
  have pair := CubicGirth.common_bound H miss
  by_cases tri : ∀ a b c, H.Adj a b → H.Adj b c → ¬ H.Adj c a
  · have sizes := CubicGirth.component_size H nbr tri miss cut
    have bound := CubicCount.eight_elevenths H hm edge sizes
    exact miss (noTri n H hm edge nbr pair cut tri sizes (by simpa using bound))
  · push Not at tri
    have bound := CubicCount.two_thirds H hm edge nbr
    apply miss
    apply hasTri n H hm edge nbr pair cut tri _ (by simpa using bound)
    intro m inst hm' e side short
    exact miss (E64Ring.triangle_ring_power hm' e side short)

end

end OMA.R_Erdos64_erdos_64_R2
