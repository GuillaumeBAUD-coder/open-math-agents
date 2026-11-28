import OMAReductions.R_RamseyNumbers_ramsey_number_three_eight_R1
import Mathlib.Data.Finset.Option
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A sparse 20-vertex base for the upper bound on R(3,8)

The first two inputs are the statements already proved in the (3,8) and (3,9)
reductions. The last two are finite gluing problems. For the nonregular case,
we choose the root by summing the exact deficiency identity over all vertices.
For a regular graph the base and all row sizes are fixed by the degree.

The counting and contact lemmas adapt the R(3,9) reduction by sturdy4days
and the neighborhood identities by physbuzz.
-/
open SimpleGraph RamseyNumbers Finset
namespace Ramsey28Contacts
theorem sum_neighbor_degrees {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∑ v, ∑ w ∈ G.neighborFinset v, G.degree w) = ∑ v, G.degree v ^ 2 := by
  simp only [SimpleGraph.neighborFinset_eq_filter,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  calc
    (∑ v, if G.Adj v w then G.degree w else 0) =
        ∑ v ∈ univ.filter (G.Adj w), G.degree w := by
          rw [Finset.sum_filter]
          simp only [G.adj_comm]
    _ = G.degree w^2 := by
      rw [← G.neighborFinset_eq_filter,Finset.sum_const,G.card_neighborFinset_eq_degree,nsmul_eq_mul,pow_two]
      norm_cast

theorem extract_anti {n m k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : G.CliqueFree 3) (ind : Gᶜ.CliqueFree (k+1)) (v : Fin n)
    (enough : m≤Gᶜ.degree v) :
    let D := G.induce ((Gᶜ.neighborFinset v : Finset (Fin n)) : Set (Fin n))
    ∃ (K : SimpleGraph (Fin m)) (_ : DecidableRel K.Adj),
      K.CliqueFree 3 ∧ Kᶜ.CliqueFree k ∧ K.edgeFinset.card≤D.edgeFinset.card := by
  classical
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set (Fin n))
  have card : m ≤ Fintype.card B := by rw [Fintype.card_coe]; exact enough
  obtain ⟨f,_⟩ := Function.Embedding.exists_of_card_le_finset (α:=Fin m) (s:=(univ : Finset B)) (by simpa using card)
  let K := D.comap f
  let e : K ↪g D := SimpleGraph.Embedding.comap f D
  let into : D ↪g G := SimpleGraph.Embedding.comap (Function.Embedding.subtype (· ∈ B)) G
  let all : K ↪g G := e.trans into
  have transport := Fintype.card_le_of_embedding e.toCopy.mapEdgeSet
  rw [K.card_edgeSet,D.card_edgeSet] at transport
  refine ⟨K,inferInstance,CliqueFree.comap all.isContained tri,?_,transport⟩
  intro S cl
  have mapped : Gᶜ.IsNClique k (S.map all.toEmbedding) := by
    refine ⟨?_,(card_map _).trans cl.card_eq⟩
    intro x hx y hy ne
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact (SimpleGraph.Embedding.complEquiv all).map_adj_iff.mpr
      (cl.isClique ha hb (fun h => ne (congrArg all h)))
  apply ind _ (mapped.insert (a:=v) ?_)
  intro w hw
  obtain ⟨i,_,rfl⟩ := mem_map.mp hw
  exact (Gᶜ.mem_neighborFinset _ _).mp (f i).property

lemma lift_card {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hi : Gᶜ.CliqueFree 8) (S : Finset (Gᶜ.neighborFinset v))
    (cl : ((G.induce ((Gᶜ.neighborFinset v : Finset V) : Set V))ᶜ).IsClique S) :
    S.card ≤ 6 := by
  classical
  let B := Gᶜ.neighborFinset v
  let f : B ↪ V := Function.Embedding.subtype _
  have free : Gᶜ.IsClique (S.map f) := by
    intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact ⟨hxy,(cl ha hb (fun h => hxy (congrArg f h))).2⟩
  have hv : v ∉ S.map f := by
    intro hm
    obtain ⟨b,_,eq⟩ := mem_map.mp hm
    exact ((Gᶜ.mem_neighborFinset _ _).mp b.2).ne eq.symm
  have ext : Gᶜ.IsClique (insert v (S.map f)) := free.insert (by
    intro b hb _
    obtain ⟨i,_,rfl⟩ := mem_map.mp hb
    exact (Gᶜ.mem_neighborFinset _ _).mp i.2)
  have lim : (insert v (S.map f)).card < 8 := lt_of_not_ge (fun h =>
    hi.mono h _ ⟨by simpa only [Finset.coe_insert] using ext,rfl⟩)
  rw [card_insert_of_notMem hv,card_map] at lim
  omega

theorem neighborhood_data {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 8) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set V)
    let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
    D.CliqueFree 3 ∧ Dᶜ.CliqueFree 7 ∧
      (∀ i, Dᶜ.IsClique (A i)) ∧
      (∀ (J : Finset N) (S : Finset B), Dᶜ.IsClique S → (∀ a ∈ J, Disjoint (A a) S) → J.card+S.card≤7) ∧
      N.card + (∑ a, (A a).card) ≤ ∑ a ∈ N, G.degree a := by
  classical
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set V)
  let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
  let f : B ↪ V := Function.Embedding.subtype _
  let g : N ↪ V := Function.Embedding.subtype _
  let em : D ↪g G := SimpleGraph.Embedding.comap f G
  have nd (a : N) := (G.mem_neighborFinset v a.val).mp a.2
  have bd (a : B) := (Gᶜ.mem_neighborFinset v a.val).mp a.2
  have split (a : N) (b : B) : a.val≠b.val := fun eq => (bd b).2 (eq ▸ nd a)
  have nr (a b : N) : ¬G.Adj a.val b.val := by
    intro h
    exact G.isIndepSet_neighborSet_of_triangleFree ht v (nd a) (nd b) h.ne h
  change D.CliqueFree 3 ∧ Dᶜ.CliqueFree 7 ∧ (∀ i, Dᶜ.IsClique (A i)) ∧ _ ∧ _
  refine ⟨CliqueFree.comap em.isContained ht,?_,?_,?_,?_⟩
  · intro S hS
    have h := lift_card G v hi S hS.isClique
    have eq := hS.card_eq
    omega
  · intro i a ha b hb hne
    refine ⟨hne,?_⟩
    intro h
    exact G.isIndepSet_neighborSet_of_triangleFree ht i.val (mem_filter.mp ha).2 (mem_filter.mp hb).2
      (Subtype.val_injective.ne hne) h
  · intro J S cl dis
    let X := J.map g
    let Y := S.map f
    have apart : Disjoint X Y := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨a,_,rfl⟩ := mem_map.mp hx
      obtain ⟨b,_,eq⟩ := mem_map.mp hy
      exact split a b eq.symm
    have sx : Gᶜ.IsClique X := by
      intro u hu w hw hne
      obtain ⟨a,_,rfl⟩ := mem_map.mp hu
      obtain ⟨b,_,rfl⟩ := mem_map.mp hw
      exact ⟨hne,nr a b⟩
    have sy : Gᶜ.IsClique Y := by
      intro u hu w hw hne
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
      exact ⟨hne,(cl ha hb (fun h => hne (congrArg f h))).2⟩
    have cross (u : V) (hu : u∈X) (w : V) (hw : w∈Y) : Gᶜ.Adj u w := by
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
      exact ⟨split a b,fun h => Finset.disjoint_left.mp (dis a ha) (mem_filter.mpr ⟨mem_univ _,h⟩) hb⟩
    have full : Gᶜ.IsClique (X ∪ Y) := by
      intro u hu w hw hne
      rcases hu with hu|hu <;> rcases hw with hw|hw
      · exact sx hu hw hne
      · exact cross _ hu _ hw
      · exact (cross _ hw _ hu).symm
      · exact sy hu hw hne
    have lim : (X ∪ Y).card < 8 := lt_of_not_ge (fun h =>
      hi.mono h _ ⟨by simpa only [Finset.coe_union] using full,rfl⟩)
    rw [card_union_of_disjoint apart,card_map,card_map] at lim
    omega
  · have each (a : N) : 1 + (A a).card ≤ G.degree a.val := by
      let Y := (A a).map f
      have nv : v ∉ Y := by
        rintro mem
        obtain ⟨b,_,eq⟩ := mem_map.mp mem
        exact (bd b).1 eq.symm
      have sub : insert v Y ⊆ G.neighborFinset a.val := by
        intro w hw
        rcases mem_insert.mp hw with rfl|mem
        · exact (G.mem_neighborFinset _ _).mpr (nd a).symm
        · obtain ⟨b,hb,rfl⟩ := mem_map.mp mem
          exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp hb).2
      have le := card_le_card sub
      rw [card_insert_of_notMem nv,card_map,G.card_neighborFinset_eq_degree] at le
      omega
    have total := Finset.sum_le_sum (s := (univ : Finset N)) (fun a _ => each a)
    change N.card + (∑ a : N,(A a).card) ≤ ∑ a ∈ N,G.degree a
    rw [← Finset.sum_coe_sort N (fun i => G.degree i)]
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.mul_one,
      Fintype.card_coe,Nat.cast_id] using total


theorem row_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ht : G.CliqueFree 3) (v : Fin n) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let A (i : N) := (univ : Finset B).filter (fun x => G.Adj i.val x.val)
    ∀ i : N, (A i).card+1=G.degree i.val := by
  intro N B A i
  let f : B ↪ Fin n := ⟨Subtype.val,Subtype.val_injective⟩
  have root := (G.mem_neighborFinset ..).mp i.property
  have eq : (A i).map f=(G.neighborFinset i.val).erase v := by
    ext y
    constructor
    · intro h
      obtain ⟨x,hx,rfl⟩ := mem_map.mp h
      exact mem_erase.mpr ⟨((Gᶜ.mem_neighborFinset ..).mp x.property).ne.symm,
        (G.mem_neighborFinset ..).mpr (mem_filter.mp hx).2⟩
    · intro h
      obtain ⟨ne,ha⟩ := mem_erase.mp h
      have adj := (G.mem_neighborFinset ..).mp ha
      have notAdj : ¬G.Adj v y := fun hit =>
        G.isIndepSet_neighborSet_of_triangleFree ht v root hit adj.ne adj
      exact mem_map.mpr ⟨⟨y,(Gᶜ.mem_neighborFinset ..).mpr ⟨ne.symm,notAdj⟩⟩,
        mem_filter.mpr ⟨mem_univ _,adj⟩,rfl⟩
  rw [←card_map (f:=f) (s:=A i),eq,card_erase_add_one ((G.mem_neighborFinset ..).mpr root.symm)]
  rfl

theorem removed_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ht : G.CliqueFree 3) (v : Fin n) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin n))
    D.edgeFinset.card+(∑ i ∈ N, G.degree i) = G.edgeFinset.card := by
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set (Fin n))
  let U : Finset (Fin n) := univ
  let W (X Y : Finset (Fin n)) := ∑ i ∈ X, ∑ j ∈ Y, (if G.Adj i j then 1 else 0 : ℕ)
  have flip (X Y) : W X Y = W Y X := by
    unfold W
    rw [Finset.sum_comm]
    simp only [G.adj_comm]
  have partition (X Y) : W X Y + W Xᶜ Y = W U Y := Finset.sum_add_sum_compl X _
  have total (X) : W X U=∑ i ∈ X, G.degree i := by
    simp [W,U,SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
  have vanish : W N N=0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    have un : ¬G.Adj a b := fun adj => G.isIndepSet_neighborSet_of_triangleFree ht v
      ((G.mem_neighborFinset _ _).mp ha) ((G.mem_neighborFinset _ _).mp hb) adj.ne adj
    simp [un]
  have complement : Nᶜ=insert v B := by
    ext x
    by_cases h : x=v
    · subst x
      simp [N]
    · simp only [N,B,mem_compl,mem_insert,G.mem_neighborFinset,Gᶜ.mem_neighborFinset,SimpleGraph.compl_adj]; tauto
  have absent : v∉B := by simp [B]
  have drop {Z : Finset (Fin n)} (isolated : ∀ j∈Z,¬G.Adj v j) : W Nᶜ Z=W B Z := by
    rw [complement]
    simp [W,sum_insert absent]
    exact fun x hx => isolated x hx
  have outside : ∀ j∈Nᶜ,¬G.Adj v j := fun j hj adj => (mem_compl.mp hj) ((G.mem_neighborFinset ..).mpr adj)
  have outB : ∀ j∈B,¬G.Adj v j := fun j hj => ((Gᶜ.mem_neighborFinset ..).mp hj).2
  have exactCut : W Nᶜ Nᶜ=W B B := (drop outside).trans ((flip B Nᶜ).trans (drop outB))
  have db : W B B = 2*D.edgeFinset.card := by
    calc
      W B B = ∑ i : B, ∑ j ∈ B, (if G.Adj i.val j then 1 else 0 : ℕ) :=
        (Finset.sum_coe_sort B _).symm
      _ = ∑ i : B, ∑ j : B, (if D.Adj i j then 1 else 0 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (Finset.sum_coe_sort B (fun j => if G.Adj i.val j then 1 else 0)).symm
      _ = ∑ i : B, D.degree i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
        exact Finset.sum_boole (R:=ℕ) (D.Adj i) univ
      _ = _ := D.sum_degrees_eq_twice_card_edges
  have p1 := partition N U
  have p2 := partition N N
  have p3 := partition N Nᶜ
  have f1 := flip Nᶜ U
  have f2 := flip N U
  have f3 := flip Nᶜ N
  have a := total N
  have b := total U
  have all : (∑ i ∈ U,G.degree i) = 2*G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  change D.edgeFinset.card+(∑ i ∈ N,G.degree i)=G.edgeFinset.card
  omega

end Ramsey28Contacts

namespace Ramsey28Contacts

-- Each neighbour of a base vertex is either another base vertex or a row.
lemma column_card (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj] (v : Fin 28) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin 28))
    let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
    ∀ x : B, D.degree x + (univ.filter fun i : N => x ∈ A i).card = G.degree x.val := by
  intro N B D A x
  let f : B ↪ Fin 28 := Function.Embedding.subtype _
  let g : N ↪ Fin 28 := Function.Embedding.subtype _
  let X := (D.neighborFinset x).map f
  let Y := ((univ : Finset N).filter fun i => x ∈ A i).map g
  have apart : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨a,_,rfl⟩ := mem_map.mp hz
    obtain ⟨i,_,eq⟩ := mem_map.mp hz'
    have h : i.val = a.val := eq
    exact ((Gᶜ.mem_neighborFinset ..).mp a.property).2 (h ▸ (G.mem_neighborFinset ..).mp i.property)
  have cover : X ∪ Y = G.neighborFinset x.val := by
    ext y
    constructor
    · intro h
      rcases mem_union.mp h with h|h
      · obtain ⟨a,ha,rfl⟩ := mem_map.mp h
        exact (G.mem_neighborFinset ..).mpr ((D.mem_neighborFinset ..).mp ha)
      · obtain ⟨i,hi,rfl⟩ := mem_map.mp h
        exact (G.mem_neighborFinset ..).mpr (G.adj_symm (mem_filter.mp (mem_filter.mp hi).2).2)
    · intro h
      have xy := (G.mem_neighborFinset ..).mp h
      by_cases vy : G.Adj v y
      · let i : N := ⟨y,(G.mem_neighborFinset ..).mpr vy⟩
        exact mem_union_right _ (mem_map.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,xy.symm⟩⟩,rfl⟩)
      · have ne : v ≠ y := by
          rintro rfl
          exact ((Gᶜ.mem_neighborFinset ..).mp x.property).2 xy.symm
        let a : B := ⟨y,(Gᶜ.mem_neighborFinset ..).mpr ⟨ne,vy⟩⟩
        exact mem_union_left _ (mem_map.mpr ⟨a,(D.mem_neighborFinset ..).mpr xy,rfl⟩)
  have h := congrArg Finset.card cover
  rw [card_union_of_disjoint apart] at h
  simpa only [X,Y,card_map,SimpleGraph.card_neighborFinset_eq_degree] using h

-- McKay and Zhang's regular-case pruning: root at a pair with four
-- common neighbours if one exists. Otherwise all pairs have at most three.
lemma regular_root (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (tri : G.CliqueFree 3) (all : ∀ x, G.degree x = 7) :
    ∃ v, let N := G.neighborFinset v
         let B := Gᶜ.neighborFinset v
         let D := G.induce (B : Set (Fin 28))
         let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
         (∃ x : B, D.degree x ≤ 3) ∨
           ((∀ i j : N, i ≠ j → ((A i) ∩ (A j)).card ≤ 2) ∧
            (∀ (i : N) (x : B), ((A i) ∩ D.neighborFinset x).card ≤ 3) ∧
            (∀ x y : B, x ≠ y →
              (D.neighborFinset x ∩ D.neighborFinset y).card +
                (univ.filter fun i : N => x ∈ A i ∧ y ∈ A i).card ≤ 3)) := by
  classical
  let common (x y : Fin 28) := G.neighborFinset x ∩ G.neighborFinset y
  by_cases somePair : ∃ x y, x ≠ y ∧ 4 ≤ (common x y).card
  · obtain ⟨v,y,ne,four⟩ := somePair
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin 28))
    let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
    obtain ⟨z,hz⟩ := Finset.card_pos.mp (by omega : 0 < (common v y).card)
    obtain ⟨vz,yz⟩ := mem_inter.mp hz
    have anti : ¬G.Adj v y := fun vy => G.isIndepSet_neighborSet_of_triangleFree tri z
      ((G.mem_neighborFinset ..).mp vz).symm ((G.mem_neighborFinset ..).mp yz).symm ne vy
    let b : B := ⟨y,(Gᶜ.mem_neighborFinset ..).mpr ⟨ne,anti⟩⟩
    let f : N ↪ Fin 28 := Function.Embedding.subtype _
    have eq : (univ.filter fun i : N => b ∈ A i).map f = common v y := by
      ext w
      constructor
      · intro h
        obtain ⟨i,hi,rfl⟩ := mem_map.mp h
        exact mem_inter.mpr ⟨i.property,(G.mem_neighborFinset ..).mpr
          (G.adj_symm (mem_filter.mp (mem_filter.mp hi).2).2)⟩
      · intro h
        obtain ⟨hw,hy⟩ := mem_inter.mp h
        exact mem_map.mpr ⟨⟨w,hw⟩, mem_filter.mpr ⟨mem_univ _,mem_filter.mpr
          ⟨mem_univ _,((G.mem_neighborFinset ..).mp hy).symm⟩⟩,rfl⟩
    have contacts := congrArg Finset.card eq
    rw [card_map] at contacts
    have col := column_card G v b
    change D.degree b + (univ.filter fun i : N => b ∈ A i).card = G.degree b.val at col
    rw [all] at col
    have small : D.degree b ≤ 3 := by omega
    exact ⟨v,Or.inl ⟨b,small⟩⟩
  · have cap (x y : Fin 28) (ne : x ≠ y) : (common x y).card ≤ 3 := by
      by_contra! h
      exact somePair ⟨x,y,ne,h⟩
    let v : Fin 28 := 0
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin 28))
    let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
    let f : B ↪ Fin 28 := Function.Embedding.subtype _
    let g : N ↪ Fin 28 := Function.Embedding.subtype _
    have apart (i : N) (x : B) : i.val ≠ x.val := by
      intro eq
      exact ((Gᶜ.mem_neighborFinset ..).mp x.property).2 (eq ▸ (G.mem_neighborFinset ..).mp i.property)
    refine ⟨v,Or.inr ⟨?_,?_,?_⟩⟩
    · intro i j ne
      let S := A i ∩ A j
      have absent : v ∉ S.map f := by
        rintro h
        obtain ⟨b,_,eq⟩ := mem_map.mp h
        exact ((Gᶜ.mem_neighborFinset ..).mp b.property).1 eq.symm
      have sub : insert v (S.map f) ⊆ common i.val j.val := by
        intro w h
        rcases mem_insert.mp h with rfl|h
        · exact mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp i.property).symm,
            (G.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp j.property).symm⟩
        · obtain ⟨b,hb,rfl⟩ := mem_map.mp h
          obtain ⟨u,t⟩ := mem_inter.mp hb
          exact mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr (mem_filter.mp u).2,
            (G.mem_neighborFinset ..).mpr (mem_filter.mp t).2⟩
      have h := (card_le_card sub).trans (cap i.val j.val (Subtype.val_injective.ne ne))
      rw [card_insert_of_notMem absent,card_map] at h
      change S.card ≤ 2
      omega
    · intro i x
      let S := A i ∩ D.neighborFinset x
      have sub : S.map f ⊆ common i.val x.val := by
        intro w hw
        obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
        obtain ⟨u,t⟩ := mem_inter.mp hb
        exact mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr (mem_filter.mp u).2,
          (G.mem_neighborFinset ..).mpr ((D.mem_neighborFinset ..).mp t)⟩
      simpa only [card_map] using (card_le_card sub).trans (cap i.val x.val (apart i x))
    · intro x y ne
      let S := D.neighborFinset x ∩ D.neighborFinset y
      let J := (univ : Finset N).filter fun i => x ∈ A i ∧ y ∈ A i
      have dis : Disjoint (S.map f) (J.map g) := by
        apply Finset.disjoint_left.mpr
        intro w hx hy
        obtain ⟨b,_,rfl⟩ := mem_map.mp hx
        obtain ⟨i,_,eq⟩ := mem_map.mp hy
        exact apart i b eq
      have sub : S.map f ∪ J.map g ⊆ common x.val y.val := by
        intro w hw
        rcases mem_union.mp hw with hw|hw
        · obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
          obtain ⟨u,t⟩ := mem_inter.mp hb
          exact mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr ((D.mem_neighborFinset ..).mp u),
            (G.mem_neighborFinset ..).mpr ((D.mem_neighborFinset ..).mp t)⟩
        · obtain ⟨i,hi,rfl⟩ := mem_map.mp hw
          obtain ⟨u,t⟩ := (mem_filter.mp hi).2
          exact mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr (G.adj_symm (mem_filter.mp u).2),
            (G.mem_neighborFinset ..).mpr (G.adj_symm (mem_filter.mp t).2)⟩
      simpa only [card_union_of_disjoint dis,card_map] using
        (card_le_card sub).trans (cap x.val y.val (Subtype.val_injective.ne ne))

lemma grouped (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (range : ∀ v, 5 ≤ G.degree v ∧ G.degree v ≤ 7) (f : Nat → Nat) :
    let a (d : Nat) := (univ.filter fun v => G.degree v = d).card
    (∑ v, f (G.degree v)) = f 5*a 5 + f 6*a 6 + f 7*a 7 := by
  intro a
  have one (v : Fin 28) : f (G.degree v) =
      (if G.degree v=5 then f 5 else 0)+(if G.degree v=6 then f 6 else 0)+
      (if G.degree v=7 then f 7 else 0) := by
    obtain h|h|h : G.degree v=5 ∨ G.degree v=6 ∨ G.degree v=7 := by have := range v; omega
    all_goals simp [h]
  simpa [a,sum_add_distrib,sum_ite,Nat.mul_comm] using sum_congr (s₁:=univ) (s₂:=univ) rfl (fun v _ => one v)

-- Attach a new vertex to T. Removing it from an independent eight-set
-- leaves exactly the seven-set sought in the original statement.
theorem obstruction_of_upper (upper : IsGraphRamsey 28 3 8) :
    OMA.R_RamseyNumbers_ramsey_number_three_eight_R1.H2 := by
  classical
  intro H tri ind T independent _ _
  let adj : Option (Fin 27) → Option (Fin 27) → Prop
    | none, none => False
    | some x, none | none, some x => x ∈ T
    | some x, some y => H.Adj x y
  let G : SimpleGraph (Option (Fin 27)) :=
    { Adj := adj
      symm := ⟨by intro x y h; cases x <;> cases y <;> first | exact h | exact H.adj_symm h⟩
      loopless := ⟨by intro x; cases x <;> first | exact id | exact H.loopless.irrefl _⟩ }
  have pull {S : Finset (Option (Fin 27))} (h : G.IsClique S) : H.IsClique S.eraseNone := by
    intro x hx y hy ne
    exact h (mem_eraseNone.mp hx) (mem_eraseNone.mp hy) ((Option.some_injective _).ne ne)
  have ht : G.CliqueFree 3 := by
    intro S h
    by_cases hn : none ∈ S
    · have card : S.eraseNone.card = 2 := by rw [card_eraseNone_of_mem hn,h.card_eq]
      obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp (by omega : 1 < S.eraseNone.card)
      have inside (x) (hx : x ∈ S.eraseNone) : x ∈ T :=
        h.isClique hn (mem_eraseNone.mp hx) (by simp)
      exact (independent (inside a ha) (inside b hb) ne).2 (pull h.isClique ha hb ne)
    · exact tri _ ⟨pull h.isClique,(card_eraseNone_of_not_mem hn).trans h.card_eq⟩
  let e := Fintype.equivFinOfCardEq (α := Option (Fin 27)) (n := 28) (by simp)
  let K := G.comap e.symm.toEmbedding
  let emb : K ↪g G := SimpleGraph.Embedding.comap e.symm.toEmbedding G
  have existsSet : ¬ Gᶜ.CliqueFree 8 := fun free =>
    upper K ⟨CliqueFree.comap emb.isContained ht,CliqueFree.comap (SimpleGraph.Embedding.complEquiv emb).isContained free⟩
  obtain ⟨S,h⟩ : ∃ S, Gᶜ.IsNClique 8 S := by
    by_contra! no
    exact existsSet no
  have cl : Hᶜ.IsClique S.eraseNone := by
    intro x hx y hy ne
    exact ⟨ne,(h.isClique (mem_eraseNone.mp hx) (mem_eraseNone.mp hy) ((Option.some_injective _).ne ne)).2⟩
  have hn : none ∈ S := by
    by_contra no
    exact ind _ ⟨cl,(card_eraseNone_of_not_mem no).trans h.card_eq⟩
  refine ⟨S.eraseNone,⟨cl,by rw [card_eraseNone_of_mem hn,h.card_eq]⟩,Finset.disjoint_left.mpr ?_⟩
  intro x hx tx
  exact (h.isClique hn (mem_eraseNone.mp hx) (by simp)).2 tx

end Ramsey28Contacts

namespace OMA.R_RamseyNumbers_ramsey_number_three_eight_R1_H2_R1
open Ramsey28Contacts

-- These first two inputs have existing, separately checked OMA proofs.
def H1 : Prop := IsGraphRamsey 23 3 7

def H2 : Prop :=
  ∀ (n : ℕ), 19 ≤ n → n ≤ 22 → ∀ (D : SimpleGraph (Fin n)) [DecidableRel D.Adj],
    D.CliqueFree 3 → Dᶜ.CliqueFree 7 →
    (if n=22 then 59 else if n=21 then 51 else if n=20 then 44 else 37) ≤ D.edgeFinset.card

-- Nonregular case. The row sizes, column degrees and total edge budget
-- restrict the seven independent sets that could form the neighbourhood.
def H3 : Prop :=
  ∀ (V I : Type) [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I],
    Fintype.card V = 20 → Fintype.card I = 7 →
    ∀ (D : SimpleGraph V) [DecidableRel D.Adj], D.CliqueFree 3 → Dᶜ.CliqueFree 7 →
    44 ≤ D.edgeFinset.card → D.edgeFinset.card ≤ 48 →
    ∀ A : I → Finset V, (∀ i, Dᶜ.IsClique (A i)) →
    (∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6) →
    (∀ x, let d := D.degree x + (univ.filter fun i => x ∈ A i).card; 5 ≤ d ∧ d ≤ 7) →
    90 ≤ D.edgeFinset.card + 7 + ∑ i, (A i).card →
    D.edgeFinset.card + 7 + ∑ i, (A i).card ≤ 97 →
    (let e := D.edgeFinset.card + 7 + ∑ i, (A i).card
     D.edgeFinset.card ≤ if e ≤ 90 then 45 else if e ≤ 92 then 46 else if e ≤ 94 then 47 else 48) →
    ∃ (J : Finset I) (S : Finset V), Dᶜ.IsClique S ∧
      (∀ i ∈ J, Disjoint (A i) S) ∧ 8 ≤ J.card + S.card

-- Regular case. Every row has six entries and each base vertex has
-- exactly seven neighbours when its entries across the rows are counted.
def H4 : Prop :=
  ∀ (V I : Type) [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I],
    Fintype.card V = 20 → Fintype.card I = 7 →
    ∀ (D : SimpleGraph V) [DecidableRel D.Adj], D.CliqueFree 3 → Dᶜ.CliqueFree 7 →
    D.edgeFinset.card = 49 → ∀ A : I → Finset V, (∀ i, Dᶜ.IsClique (A i)) →
    (∀ i, (A i).card = 6) →
    (∀ x, D.degree x + (univ.filter fun i => x ∈ A i).card = 7) →
    ((∃ x : V, D.degree x ≤ 3) ∨
      ((∀ i j : I, i ≠ j → ((A i) ∩ (A j)).card ≤ 2) ∧
       (∀ (i : I) (x : V), ((A i) ∩ D.neighborFinset x).card ≤ 3) ∧
       (∀ x y : V, x ≠ y → (D.neighborFinset x ∩ D.neighborFinset y).card +
         (univ.filter fun i : I => x ∈ A i ∧ y ∈ A i).card ≤ 3))) →
    ∃ (J : Finset I) (S : Finset V), Dᶜ.IsClique S ∧
      (∀ i ∈ J, Disjoint (A i) S) ∧ 8 ≤ J.card + S.card

open Finset

set_option maxHeartbeats 2000000 in
theorem main : H1 → H2 → H3 → H4 → OMA.R_RamseyNumbers_ramsey_number_three_eight_R1.H2 := by
  classical
  intro smaller lower sparse regular
  apply obstruction_of_upper
  rintro G ⟨tri,ind⟩
  let child (v : Fin 28) := (G.induce ((Gᶜ.neighborFinset v : Finset (Fin 28)) : Set (Fin 28))).edgeFinset.card
  have range (v : Fin 28) : 5 ≤ G.degree v ∧ G.degree v ≤ 7 := by
    have low := OMA.R_RamseyNumbers_ramsey_number_three_eight_R1.nonneighbors_lt smaller G tri ind v
    rw [G.degree_compl,Fintype.card_fin] at low
    have high := OMA.R_RamseyNumbers_ramsey_number_three_eight_R1.degree_lt G tri ind v
    omega
  let lb (d : Nat) := if d=5 then 59 else if d=6 then 51 else 44
  have localBound (v : Fin 28) : lb (G.degree v) ≤ child v := by
    let m := Gᶜ.degree v
    have hm : m = 28-1-G.degree v := by simp [m,G.degree_compl]
    have r := range v
    obtain ⟨K,di,tk,ik,sub⟩ := extract_anti (m:=m) G tri ind v le_rfl
    let := di
    have bound := lower m (by omega) (by omega) K tk ik
    have eq : (if m=22 then 59 else if m=21 then 51 else if m=20 then 44 else 37) = lb (G.degree v) := by
      dsimp [lb]
      split_ifs <;> omega
    rw [eq] at bound
    exact bound.trans sub
  have budget : (∑ v, (child v + G.degree v ^ 2)) = 28 * G.edgeFinset.card := by
    have h := sum_congr (s₁:=univ) (s₂:=univ) rfl (fun v _ => removed_eq G tri v)
    change (∑ v, (child v + ∑ w ∈ G.neighborFinset v, G.degree w)) = ∑ _ : Fin 28, G.edgeFinset.card at h
    simpa only [sum_add_distrib,sum_neighbor_degrees,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using h
  let a (d : Nat) := (univ.filter fun v => G.degree v = d).card
  have count : 28 = a 5+a 6+a 7 := by simpa [a] using grouped G range (fun _ => 1)
  have hand : 2*G.edgeFinset.card = 5*a 5+6*a 6+7*a 7 := by
    simpa only [id_eq,G.sum_degrees_eq_twice_card_edges,a] using grouped G range id
  have profile : 84*a 5+87*a 6+93*a 7 ≤ 28*G.edgeFinset.card := by
    have h := sum_le_sum (s:=univ) (fun v _ => Nat.add_le_add_right (localBound v) (G.degree v ^ 2))
    rw [budget] at h
    have group := grouped G range (fun d => lb d + d^2)
    change (∑ v, (lb (G.degree v) + G.degree v^2)) = 84*a 5+87*a 6+93*a 7 at group
    exact group ▸ h
  have edges : 90 ≤ G.edgeFinset.card := by omega
  let threshold := if G.edgeFinset.card ≤ 90 then 45 else if G.edgeFinset.card ≤ 92 then 46 else if G.edgeFinset.card ≤ 94 then 47 else 48
  let pruning (v : Fin 28) :=
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin 28))
    let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
    ((∃ x : B, D.degree x ≤ 3) ∨
      ((∀ i j : N, i ≠ j → ((A i) ∩ (A j)).card ≤ 2) ∧
       (∀ (i : N) (x : B), ((A i) ∩ D.neighborFinset x).card ≤ 3) ∧
       (∀ x y : B, x ≠ y → (D.neighborFinset x ∩ D.neighborFinset y).card +
         (univ.filter fun i : N => x ∈ A i ∧ y ∈ A i).card ≤ 3)))
  have choose : ∃ v, G.degree v = 7 ∧
      ((child v ≤ threshold ∧ G.edgeFinset.card ≤ 97) ∨ ((∀ w, G.degree w = 7) ∧ child v = 49 ∧ pruning v)) := by
    by_cases all : ∀ w, G.degree w = 7
    · have hand' := G.sum_degrees_eq_twice_card_edges
      simp [all] at hand'
      obtain ⟨v,hpr⟩ := regular_root G tri all
      have eq := removed_eq G tri v
      change child v + (∑ w ∈ G.neighborFinset v, G.degree w) = G.edgeFinset.card at eq
      simp [all] at eq
      exact ⟨v,all v,Or.inr ⟨all,by omega,hpr⟩⟩
    · obtain ⟨w,hw⟩ : ∃ w, G.degree w ≠ 7 := by simpa only [not_forall] using all
      have less := sum_lt_sum (s:=univ) (g:=fun _ : Fin 28 => 7) (fun i _ => (range i).2)
        ⟨w,mem_univ _,lt_of_le_of_ne (range w).2 hw⟩
      simp only [G.sum_degrees_eq_twice_card_edges,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at less
      suffices found : ∃ v, G.degree v=7 ∧ child v≤threshold by
        obtain ⟨v,hd,hc⟩ := found
        exact ⟨v,hd,Or.inl ⟨hc,by omega⟩⟩
      by_contra! none
      let forced (d : Nat) := if d=7 then threshold+1 else lb d
      have cost (i : Fin 28) : forced (G.degree i) + G.degree i^2 ≤ child i + G.degree i^2 := by
        apply Nat.add_le_add_right
        by_cases hd : G.degree i=7
        · simpa [forced,hd] using Nat.succ_le_of_lt (none i hd)
        · simpa [forced,hd] using localBound i
      have impossible := sum_le_sum (s:=univ) (fun i _ => cost i)
      rw [budget] at impossible
      have groupedCost := grouped G range (fun d => forced d + d^2)
      change (∑ i, (forced (G.degree i)+G.degree i^2)) =
        84*a 5+87*a 6+(threshold+1+49)*a 7 at groupedCost
      rw [groupedCost] at impossible
      dsimp [threshold] at impossible
      split_ifs at impossible <;> omega
  obtain ⟨v,hd,casesV⟩ := choose
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set (Fin 28))
  let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
  have hn : Fintype.card N = 7 := (Fintype.card_coe _).trans hd
  have hb : Fintype.card B = 20 := by
    rw [Fintype.card_coe]
    change Gᶜ.degree v = 20
    simp [G.degree_compl,hd]
  obtain ⟨dt,di,rows,avoid,_⟩ := neighborhood_data G v tri ind
  have row (i : N) : (A i).card+1=G.degree i.val := row_card G tri v i
  have col (x : B) : D.degree x+(univ.filter fun i : N => x ∈ A i).card=G.degree x.val := column_card G v x
  have total : D.edgeFinset.card+7+(∑ i, (A i).card) = G.edgeFinset.card := by
    have eq := removed_eq G tri v
    change D.edgeFinset.card+(∑ i ∈ N, G.degree i)=G.edgeFinset.card at eq
    rw [←sum_coe_sort N (fun i => G.degree i)] at eq
    have rsum := sum_congr (s₁:=univ) (s₂:=univ) rfl (fun i _ => row i)
    simp only [sum_add_distrib,sum_const,card_univ,hn,nsmul_eq_mul,Nat.cast_id,mul_one] at rsum
    omega
  have witness : ∃ (J : Finset N) (S : Finset B), Dᶜ.IsClique S ∧
      (∀ i ∈ J, Disjoint (A i) S) ∧ 8 ≤ J.card + S.card := by
    rcases casesV with ⟨upper,cap⟩ | ⟨all,size,hpr⟩
    · have low := localBound v
      rw [hd] at low
      have capChild : threshold ≤ 48 := by dsimp [threshold]; split_ifs <;> decide
      apply sparse B N hb hn D dt di low (upper.trans capChild) A rows
      · intro i
        have := row i
        have := range i.val
        omega
      · intro x
        change 5 ≤ D.degree x + _ ∧ D.degree x + _ ≤ 7
        rw [col x]
        exact range x.val
      · omega
      · omega
      · simpa only [total] using upper
    · apply regular B N hb hn D dt di size A rows
      · intro i
        have := row i
        rw [all] at this
        omega
      · intro x
        exact (col x).trans (all _)
      · exact hpr
  obtain ⟨J,S,cl,dis,big⟩ := witness
  have small := avoid J S cl dis
  omega

end OMA.R_RamseyNumbers_ramsey_number_three_eight_R1_H2_R1
