import FormalConjectures.Wikipedia.ReconstructionConjecture

import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
/-!
# Rooted branches of a tree

The branches at a vertex are the connected components after deleting it,
each rooted at its unique neighbor of the deleted vertex.
-/

open SimpleGraph
open scoped BigOperators

namespace TreeBranches

abbrev Deleted {V : Type*} (r : V) := ({r}ᶜ : Set V)

abbrev cardAt {V : Type*} (G : SimpleGraph V) (r : V) : SimpleGraph (Deleted r) :=
  G.induce {r}ᶜ

abbrev Branch {V : Type*} (G : SimpleGraph V) (r : V) := (cardAt G r).ConnectedComponent

abbrev BranchGraph {V : Type*} {G : SimpleGraph V} {r : V} (C : Branch G r) :=
  C.toSimpleGraph

theorem existsUnique_attachment {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    (r : V) (C : Branch G r) :
    ∃! x : C.supp, G.Adj r x.val.val := by
  classical
  have ⟨z,hz⟩ := C.nonempty_supp
  obtain ⟨p,hp⟩ := hG.connected.exists_isPath r z.val
  have next (w : V) (q : G.Walk r w) (hq : q.IsPath) (hw : w ≠ r) :
      ∃ y, G.Adj r y ∧ ∃ t : G.Walk y w, r ∉ t.support := by
    cases q with
    | nil => exact (hw rfl).elim
    | @cons _ y _ hadj q => exact ⟨y,hadj,q,((Walk.cons_isPath_iff hadj q).mp hq).2⟩
  obtain ⟨y,hadj,p,hav⟩ := next z.val p hp z.property
  have hs : ∀ x ∈ p.support, x ∈ ({r}ᶜ : Set V) := by
    intro x hx
    simpa using show x ≠ r from fun he => hav (he ▸ hx)
  let y' : Deleted r := ⟨y,hs _ p.start_mem_support⟩
  have hreach : (cardAt G r).Reachable y' z := (p.induce _ hs).reachable
  have hy : y' ∈ C.supp :=
    (ConnectedComponent.sound hreach).trans hz
  refine ⟨⟨y',hy⟩,hadj,?_⟩
  intro a ha
  have hreach' : (cardAt G r).Reachable y' a.val :=
    ConnectedComponent.exact (hy.trans a.property.symm)
  obtain ⟨q,hq⟩ := hreach'.exists_isPath
  let i : cardAt G r ↪g G := SimpleGraph.Embedding.induce _
  have hq' : (q.map i.toHom).IsPath := hq.map i.injective
  have havoid : r ∉ (q.map i.toHom).support := by
    rw [Walk.support_map]
    intro h
    obtain ⟨b,hb,hbr⟩ := List.mem_map.mp h
    exact b.property (show b.val = r from hbr)
  have hpath := hq'.cons havoid (h := hadj)
  have hlast : a.val.val ∈ ((q.map i.toHom).cons hadj).support :=
    ((q.map i.toHom).cons hadj).end_mem_support
  have heq := hG.isAcyclic.eq_snd_of_adj_start hpath ha hlast
  apply Subtype.ext
  apply Subtype.ext
  exact heq.trans (Walk.snd_cons (q.map i.toHom) (show G.Adj r (i.toHom y') from hadj))

noncomputable def attachment {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    {r : V} (C : Branch G r) : C.supp :=
  Classical.choose (existsUnique_attachment hG r C)

theorem adj_attachment {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    {r : V} (C : Branch G r) : G.Adj r (attachment hG C).val.val :=
  (Classical.choose_spec (existsUnique_attachment hG r C)).1

theorem adj_iff_eq_attachment {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    {r : V} (C : Branch G r) (x : C.supp) :
    G.Adj r x.val.val ↔ x = attachment hG C := by
  refine ⟨(Classical.choose_spec (existsUnique_attachment hG r C)).2 _,?_⟩
  rintro rfl
  exact adj_attachment hG C

theorem branch_isTree {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    {r : V} (C : Branch G r) : (BranchGraph C).IsTree :=
  (hG.isAcyclic.induce _).isTree_connectedComponent C

def splitVertices {V : Type*} (G : SimpleGraph V) (r : V) :
    Deleted r ≃ Σ C : Branch G r, C.supp where
  toFun x := ⟨(cardAt G r).connectedComponentMk x,⟨x,rfl⟩⟩
  invFun x := x.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨C,x,hx⟩
    change (cardAt G r).connectedComponentMk x = C at hx
    subst C
    rfl

noncomputable def neighborBranchEquiv {V : Type*} {G : SimpleGraph V} (hG : G.IsTree) (r : V) :
    G.neighborSet r ≃ Branch G r where
  toFun x := (cardAt G r).connectedComponentMk ⟨x.val, by simpa using (show G.Adj r x.val from x.property).ne'⟩
  invFun C := ⟨(attachment hG C).val.val, adj_attachment hG C⟩
  left_inv x := by
    let y : Deleted r := ⟨x.val, by simpa using (show G.Adj r x.val from x.property).ne'⟩
    have h := (adj_iff_eq_attachment hG ((cardAt G r).connectedComponentMk y) ⟨y,rfl⟩).mp x.property
    exact Subtype.ext (congrArg (fun z => z.val.val) h.symm)
  right_inv C := (attachment hG C).property

theorem card_eq_sum_branch_sizes {V : Type*} [Finite V] (G : SimpleGraph V) (r : V)
    [Fintype (Branch G r)] :
    Nat.card V = 1 + ∑ C : Branch G r, Nat.card C.supp := by
  classical
  have h := Nat.card_congr (splitVertices G r)
  rw [Nat.card_sigma] at h
  rw [← h]
  change Nat.card V = 1 + Nat.card ({r}ᶜ : Set V)
  rw [Nat.card_coe_set_eq, Set.ncard_compl, Set.ncard_singleton]
  let _ : Nonempty V := ⟨r⟩
  have hpos : 0 < Nat.card V := Nat.card_pos (α := V)
  omega

theorem same_branch_of_adj {V : Type*} {G : SimpleGraph V} {r : V} {x y : Deleted r}
    (h : G.Adj x.val y.val) :
    (cardAt G r).connectedComponentMk x = (cardAt G r).connectedComponentMk y :=
  ConnectedComponent.sound (Adj.reachable (G := cardAt G r) h)

theorem avoid_leaf {V : Type*} {G : SimpleGraph V} {x y l : V} {p : G.Walk x y}
    (hp : p.IsPath) (hx : x ≠ l) (hy : y ≠ l)
    (hl : ∀ a b, G.Adj l a → G.Adj l b → a = b) :
    l ∉ p.support := by
  classical
  intro h
  obtain ⟨q,t,hq,ht,he⟩ := hp.mem_support_iff_exists_append.mp h
  have hq' := Walk.not_nil_of_ne hx (p := q)
  have ht' := Walk.not_nil_of_ne hy.symm (p := t)
  have ha := (q.adj_penultimate hq').symm
  have hb := t.adj_snd ht'
  have hm := hl _ _ ha hb
  have hmem₁ := q.getVert_mem_support (q.length - 1)
  have hmem₂ := t.getVert_mem_support 1
  have hnot : t.snd ≠ l := hb.ne'
  exact (he ▸ hp).ne_of_mem_support_of_append hnot hmem₁ hmem₂ hm

theorem reachable_card_iff {V : Type*} {G : SimpleGraph V} (l : V)
    (hl : ∀ a b, G.Adj l a → G.Adj l b → a = b) (x y : Deleted l) :
    (cardAt G l).Reachable x y ↔ G.Reachable x.val y.val := by
  constructor
  · exact fun h => h.map (SimpleGraph.Embedding.induce _).toHom
  · intro h
    obtain ⟨p,hp⟩ := h.exists_isPath
    have hn := avoid_leaf hp x.property y.property hl
    exact (p.induce _ (fun z hz => by simpa using (show z ≠ l from fun hzl => hn (hzl ▸ hz)))).reachable

section Reassembly

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {r : V} {s : W}

/-- Isomorphisms of the corresponding branches combine into an isomorphism
of the graph after deleting the root. -/
def combineDeleted (e : Branch G r ≃ Branch H s)
    (f : ∀ C, BranchGraph C ≃g BranchGraph (e C)) : cardAt G r ≃g cardAt H s := by
  let E := (splitVertices G r).trans
    ((Equiv.sigmaCongr e (fun C => (f C).toEquiv)).trans (splitVertices H s).symm)
  have apply_branch (C : Branch G r) (x : C.supp) :
      E x.val = (f C x).val := by
    rcases x with ⟨x,hx⟩
    change (cardAt G r).connectedComponentMk x = C at hx
    subst C
    rfl
  refine { toEquiv := E, map_rel_iff' := ?_ }
  intro x y
  let C := (cardAt G r).connectedComponentMk x
  let D := (cardAt G r).connectedComponentMk y
  let x' : C.supp := ⟨x,rfl⟩
  let y' : D.supp := ⟨y,rfl⟩
  have hx : E x = (f C x').val := apply_branch C x'
  have hy : E y = (f D y').val := apply_branch D y'
  have same_branch : (cardAt G r).Adj x y → y ∈ C.supp :=
    fun hadj => (ConnectedComponent.sound hadj.reachable).symm
  have compare (hm : y ∈ C.supp) :
      (cardAt H s).Adj (E x) (E y) ↔ (cardAt G r).Adj x y := by
    rw [hx, show E y = (f C ⟨y,hm⟩).val from apply_branch C ⟨y,hm⟩]
    exact (f C).map_rel_iff
  constructor
  · intro hadj
    have he' := ConnectedComponent.sound hadj.reachable
    rw [hx,hy] at he'
    have hleft : (cardAt H s).connectedComponentMk (f C x').val = e C := (f C x').property
    have hright : (cardAt H s).connectedComponentMk (f D y').val = e D := (f D y').property
    have hh : C = D := e.injective (hleft.symm.trans (he'.trans hright))
    exact (compare hh.symm).mp hadj
  · intro hadj
    exact (compare (same_branch hadj)).mpr hadj

theorem combineDeleted_apply (e : Branch G r ≃ Branch H s)
    (f : ∀ C, BranchGraph C ≃g BranchGraph (e C)) (C : Branch G r) (x : C.supp) :
    combineDeleted e f x.val = (f C x).val := by
  rcases x with ⟨x,hx⟩
  change (cardAt G r).connectedComponentMk x = C at hx
  subst C
  rfl

/-- A root can be added back to an isomorphism of deleted graphs if the
isomorphism preserves the vertices adjacent to the root. -/
noncomputable def extendDeleted (f : cardAt G r ≃g cardAt H s)
    (hf : ∀ x, G.Adj r x.val ↔ H.Adj s (f x).val) : G ≃g H := by
  classical
  let e₀ : ({r} : Set V) ≃ ({s} : Set W) := {
    toFun := fun _ => ⟨s,Set.mem_singleton s⟩
    invFun := fun _ => ⟨r,Set.mem_singleton r⟩
    left_inv := fun x => Subtype.ext (Set.mem_singleton_iff.mp x.property).symm
    right_inv := fun x => Subtype.ext (Set.mem_singleton_iff.mp x.property).symm }
  let E := (Equiv.Set.sumCompl ({r} : Set V)).symm.trans
    ((Equiv.sumCongr e₀ f.toEquiv).trans (Equiv.Set.sumCompl ({s} : Set W)))
  have Er : E r = s := by
    simp [E, e₀, Equiv.Set.sumCompl_symm_apply_of_mem (Set.mem_singleton r)]
  have En (v : Deleted r) : E v.val = (f v).val := by
    simp [E, Equiv.Set.sumCompl_symm_apply_of_notMem v.property]
  refine {toEquiv := E, map_rel_iff' := ?_}
  intro a b
  by_cases ha : a = r <;> by_cases hb : b = r
  · subst a; subst b
    simp [Er]
  · subst a
    rw [Er,En ⟨b,hb⟩]
    exact (hf ⟨b,hb⟩).symm
  · subst b
    rw [Er,En ⟨a,ha⟩,adj_comm H,adj_comm G]
    exact (hf ⟨a,ha⟩).symm
  · rw [En ⟨a,ha⟩,En ⟨b,hb⟩]
    exact f.map_rel_iff

/-- A tree is determined with its root by its collection of rooted branches,
including their multiplicities. -/
noncomputable def combineBranches (hG : G.IsTree) (hH : H.IsTree)
    (e : Branch G r ≃ Branch H s)
    (f : ∀ C, BranchGraph C ≃g BranchGraph (e C))
    (hf : ∀ C, f C (attachment hG C) = attachment hH (e C)) : G ≃g H :=
  extendDeleted (combineDeleted e f) (fun x => by
    let C := (cardAt G r).connectedComponentMk x
    let x' : C.supp := ⟨x,rfl⟩
    change G.Adj r x'.val.val ↔ H.Adj s (combineDeleted e f x'.val).val
    rw [combineDeleted_apply e f C x',adj_iff_eq_attachment hG C,
      adj_iff_eq_attachment hH (e C),← hf C]
    exact (f C).injective.eq_iff.symm)

end Reassembly

section LeafRemoval

variable {V : Type*} {G : SimpleGraph V} {l : V}

/-- Which connected component of the original graph contains a component
after a leaf is removed. -/
def componentOfCard (l : V) (C : Branch G l) : G.ConnectedComponent :=
  C.map (SimpleGraph.Embedding.induce ({l}ᶜ : Set V)).toHom

theorem componentOfCard_on_vertex (x : Deleted l) :
    componentOfCard l ((cardAt G l).connectedComponentMk x) = G.connectedComponentMk x.val :=
  rfl

theorem componentOfCard_injective
    (hl : ∀ a b, G.Adj l a → G.Adj l b → a = b) :
    Function.Injective (componentOfCard (G := G) l) := by
  intro C D
  refine ConnectedComponent.ind₂ (G := cardAt G l) ?_ C D
  intro x y he
  rw [componentOfCard_on_vertex,componentOfCard_on_vertex,ConnectedComponent.eq] at he
  exact ConnectedComponent.sound ((reachable_card_iff l hl x y).mpr he)

/-- Each component of a leaf-deleted graph is the original component with
that leaf removed if it was present. -/
def componentOfCardIso
    (hl : ∀ a b, G.Adj l a → G.Adj l b → a = b) (C : Branch G l) :
    BranchGraph C ≃g (componentOfCard l C).toSimpleGraph.induce {x | x.val ≠ l} := by
  refine {toEquiv := {
    toFun := fun x => ⟨⟨x.val.val,?_⟩,x.val.property⟩
    invFun := fun x => ⟨⟨x.val.val,x.property⟩,?_⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl } , map_rel_iff' := Iff.rfl }
  · change G.connectedComponentMk x.val.val = componentOfCard l C
    rw [← componentOfCard_on_vertex]
    exact congrArg (componentOfCard l) x.property
  · change (cardAt G l).connectedComponentMk ⟨x.val.val,x.property⟩ = C
    apply componentOfCard_injective hl
    rw [componentOfCard_on_vertex]
    exact x.val.property

noncomputable def componentOfCardEquiv
    (hl : ∀ a b, G.Adj l a → G.Adj l b → a = b) :
    Branch G l ≃ {C : G.ConnectedComponent // ∃ x : C.supp, x.val ≠ l} := by
  let f (C : Branch G l) :
      {C : G.ConnectedComponent // ∃ x : C.supp, x.val ≠ l} :=
    ⟨componentOfCard l C,by
      obtain ⟨x,hx⟩ := C.nonempty_supp
      exact ⟨(componentOfCardIso hl C ⟨x,hx⟩).val,
        (componentOfCardIso hl C ⟨x,hx⟩).property⟩⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro X Y h
    exact componentOfCard_injective hl (congrArg Subtype.val h)
  · rintro ⟨C,x,hx⟩
    refine ⟨(cardAt G l).connectedComponentMk ⟨x.val,hx⟩,Subtype.ext ?_⟩
    exact x.property

end LeafRemoval

section TwoVertices

variable {V : Type*} {G : SimpleGraph V} {r l : V}

def switchCards (h : r ≠ l) :
    cardAt (cardAt G l) (⟨r,h⟩ : Deleted l) ≃g
      cardAt (cardAt G r) (⟨l,h.symm⟩ : Deleted r) where
  toEquiv := {
    toFun := fun x => ⟨⟨x.val.val,fun hr => x.property (Subtype.ext hr)⟩,
      fun hl => x.val.property (congrArg Subtype.val hl)⟩
    invFun := fun x => ⟨⟨x.val.val,fun hl => x.property (Subtype.ext hl)⟩,
      fun hr => x.val.property (congrArg Subtype.val hr)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

def restrictComponentIso {A B : Type*} {X : SimpleGraph A} {Y : SimpleGraph B}
    (e : X ≃g Y) (C : X.ConnectedComponent) :
    C.toSimpleGraph ≃g (e.connectedComponentEquiv C).toSimpleGraph where
  toEquiv := C.isoEquivSupp e
  map_rel_iff' := e.map_rel_iff

abbrev removedInBranch (h : r ≠ l) : Deleted r := ⟨l,h.symm⟩

def newRoot (h : r ≠ l) : Deleted l := ⟨r,h⟩

def branchAfterDeleteIndex (h : r ≠ l)
    (C : Branch (cardAt G l) (newRoot h)) :
    Branch (cardAt G r) (removedInBranch h) :=
  (switchCards (G := G) h).connectedComponentEquiv C

def survivingBranch (h : r ≠ l) (C : Branch (cardAt G l) (newRoot h)) : Branch G r :=
  componentOfCard (removedInBranch h) (branchAfterDeleteIndex h C)

theorem leaf_unique_in_card (h : r ≠ l) (hl : ∀ a b, G.Adj l a → G.Adj l b → a = b) :
    ∀ a b, (cardAt G r).Adj (removedInBranch h) a →
      (cardAt G r).Adj (removedInBranch h) b → a = b :=
  fun _ _ ha hb => Subtype.ext (hl _ _ ha hb)

noncomputable def branchOfLeafCardEquiv (h : r ≠ l)
    (hl : ∀ a b, G.Adj l a → G.Adj l b → a = b) :
    Branch (cardAt G l) (newRoot h) ≃
      {C : Branch G r // ∃ x : C.supp, x.val.val ≠ l} :=
  ((switchCards (G := G) h).connectedComponentEquiv.trans
    (componentOfCardEquiv (leaf_unique_in_card h hl))).trans
    (Equiv.subtypeEquivRight (fun _ => exists_congr (fun _ => not_congr Subtype.ext_iff)))

/-- A branch of a leaf card matches an original branch, with the leaf removed
if it belonged to that branch. -/
def branchOfLeafCardIso (h : r ≠ l)
    (hl : ∀ a b, G.Adj l a → G.Adj l b → a = b)
    (C : Branch (cardAt G l) (newRoot h)) :
    BranchGraph C ≃g (BranchGraph (survivingBranch h C)).induce {x | x.val.val ≠ l} := by
  let C' := branchAfterDeleteIndex h C
  let C₀ := survivingBranch h C
  let δ := componentOfCardIso (leaf_unique_in_card h hl) C'
  have hs : ({x | x.val ≠ removedInBranch h} : Set C₀.supp) = {x | x.val.val ≠ l} := by
    ext x
    exact not_congr Subtype.ext_iff
  let e : (BranchGraph C₀).induce {x | x.val ≠ removedInBranch h} ≃g
      (BranchGraph C₀).induce {x | x.val.val ≠ l} :=
    {toEquiv := Equiv.setCongr hs, map_rel_iff' := Iff.rfl}
  exact (restrictComponentIso (switchCards h) C).trans (δ.trans e)

theorem branchOfLeafCardIso_vertex (h : r ≠ l)
    (hl : ∀ a b, G.Adj l a → G.Adj l b → a = b)
    (C : Branch (cardAt G l) (newRoot h)) (x : C.supp) :
    (branchOfLeafCardIso h hl C x).val.val.val = x.val.val.val := by
  rfl

theorem branchOfLeafCardIso_root (h : r ≠ l)
    (hl : ∀ a b, G.Adj l a → G.Adj l b → a = b)
    (hG : G.IsTree) (hCard : (cardAt G l).IsTree)
    (C : Branch (cardAt G l) (newRoot h)) :
    (branchOfLeafCardIso h hl C (attachment hCard C)).val =
      attachment hG (survivingBranch h C) := by
  apply (adj_iff_eq_attachment hG _ _).mp
  rw [branchOfLeafCardIso_vertex]
  exact adj_attachment hCard C

end TwoVertices

end TreeBranches

/-
A rooted branch multiset can be recovered from its single-leaf deletions
when there are at least two branches. The largest-size argument in
Theorem 2.1 of Kostochka, Nahvi, West, and Zirlin motivates this formulation:
https://dwest.web.illinois.edu/pubs/tree3rec.pdf
-/

namespace RootedBranchDeck

open Multiset

def insertOption {α : Type*} (next : Option α) (a : Multiset α) : Multiset α :=
  next.elim a (fun z => z ::ₘ a)

/-- A card is obtained by shortening one branch or removing a singleton branch. -/
def cards {α : Type*} (trim : α → Option α → Prop) (a : Multiset α) : Set (Multiset α) :=
  {c | ∃ x y r, a = x ::ₘ r ∧ trim x y ∧ c = insertOption y r}

private theorem survives {α : Type*} {trim : α → Option α → Prop}
    (hex : ∀ x, ∃ y, trim x y) {a : Multiset α} (ha : 2 ≤ a.card) {x : α} (hx : x ∈ a) :
    ∃ c ∈ cards trim a, x ∈ c := by
  classical
  obtain ⟨s,hs⟩ := Multiset.exists_cons_of_mem hx
  have hpos : 0 < s.card := by
    rw [hs,Multiset.card_cons] at ha
    omega
  obtain ⟨z,hz⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  obtain ⟨t,ht⟩ := Multiset.exists_cons_of_mem hz
  obtain ⟨y,hy⟩ := hex z
  refine ⟨insertOption y (x ::ₘ t), ⟨z,y,x ::ₘ t,?_,hy,rfl⟩,?_⟩
  · rw [hs,ht,Multiset.cons_swap]
  · cases y <;> simp [insertOption]

private theorem option_ne_of_trim {α : Type*} {size : α → ℕ} {trim : α → Option α → Prop}
    (htrim : ∀ x y, trim x y → y.elim 0 size + 1 = size x) {x z : α} {y : Option α}
    (h : trim z y) (hs : size z ≤ size x) : y ≠ some x := by
  intro he
  subst y
  have hh := htrim _ _ h
  simp at hh
  omega

private theorem count_insertOption_of_ne {α : Type*} [DecidableEq α] {x : α}
    {y : Option α} (h : y ≠ some x) (m : Multiset α) :
    (insertOption y m).count x = m.count x := by
  cases y with
  | none => rfl
  | some y =>
    change (y ::ₘ m).count x = m.count x
    apply Multiset.count_cons_of_ne
    intro hxy
    exact h (congrArg some hxy.symm)

private theorem count_on_card {α : Type*} [DecidableEq α] {size : α → ℕ}
    {trim : α → Option α → Prop} (htrim : ∀ x y, trim x y → y.elim 0 size + 1 = size x)
    {a c : Multiset α} {x : α} (hmax : ∀ z ∈ a, size z ≤ size x)
    (hc : c ∈ cards trim a) :
    c.count x ≤ a.count x ∧ a.count x ≤ c.count x + 1 := by
  obtain ⟨z,y,r,rfl,hy,rfl⟩ := hc
  rw [count_insertOption_of_ne (option_ne_of_trim htrim hy (hmax z (by simp))),
    Multiset.count_cons]
  split <;> omega

private theorem recovers_at {α : Type*} [DecidableEq α] {size : α → ℕ}
    {trim : α → Option α → Prop} (hsize : ∀ x, 0 < size x)
    (htrim : ∀ x y, trim x y → y.elim 0 size + 1 = size x)
    {a b : Multiset α} {x : α} (hmax₁ : ∀ z ∈ a, size z ≤ size x)
    (hmax₂ : ∀ z ∈ b, size z ≤ size x)
    (hx₁ : x ∈ a) (hx₂ : x ∈ b) (he : cards trim a = cards trim b)
    {y : Option α} (hy : trim x y) : a = b := by
  obtain ⟨r,hr⟩ := Multiset.exists_cons_of_mem hx₁
  obtain ⟨s,hs⟩ := Multiset.exists_cons_of_mem hx₂
  have h₁ : insertOption y r ∈ cards trim a := ⟨x,y,r,hr,hy,rfl⟩
  have h₂ : insertOption y s ∈ cards trim b := ⟨x,y,s,hs,hy,rfl⟩
  have hne := option_ne_of_trim htrim hy (le_refl (size x))
  have hc₁ := (count_on_card htrim hmax₂ (he ▸ h₁)).2
  have hc₂ := (count_on_card htrim hmax₁ (he.symm ▸ h₂)).2
  rw [count_insertOption_of_ne (x := x) hne] at hc₁ hc₂
  have hcount : a.count x = b.count x := by
    simp only [hr,hs,Multiset.count_cons_self] at hc₁ hc₂ ⊢
    omega
  have replaced {m c : Multiset α} (hm : ∀ z ∈ m, size z ≤ size x)
      (hc : c ∈ cards trim m) (heq : c.count x + 1 = m.count x) :
      ∃ y' r', m = x ::ₘ r' ∧ trim x y' ∧ c = insertOption y' r' := by
    obtain ⟨z,y',r',rfl,hy',rfl⟩ := hc
    have hh := option_ne_of_trim htrim hy' (hm z (by simp))
    rw [count_insertOption_of_ne (x := x) hh,Multiset.count_cons] at heq
    split at heq
    · rename_i hh'
      subst z
      exact ⟨y',r',rfl,hy',rfl⟩
    · omega
  have low₁ : (insertOption y r).count x + 1 = b.count x := by
    rw [← hcount,hr,count_insertOption_of_ne hne,Multiset.count_cons_self]
  have low₂ : (insertOption y s).count x + 1 = a.count x := by
    rw [hcount,hs,count_insertOption_of_ne hne,Multiset.count_cons_self]
  obtain ⟨y',s',hs',hy',he₁⟩ := replaced hmax₂ (he ▸ h₁) low₁
  obtain ⟨y'',r',hr',hy'',he₂⟩ := replaced hmax₁ (he.symm ▸ h₂) low₂
  have he_r : r = r' := (Multiset.cons_inj_right x).mp (hr.symm.trans hr')
  have he_s : s = s' := (Multiset.cons_inj_right x).mp (hs.symm.trans hs')
  subst s'
  subst r'
  cases y with
  | none =>
    have hnone : y' = none := by
      cases y' with
      | none => rfl
      | some z =>
        have hh := htrim _ _ hy
        have hh' := htrim _ _ hy'
        have hp := hsize z
        simp at hh hh'
        omega
    subst y'
    exact hr.trans (congrArg (x ::ₘ ·) he₁) |>.trans hs.symm
  | some z =>
    by_cases hsame : y' = some z
    · subst y'
      exact hr.trans (congrArg (x ::ₘ ·) ((Multiset.cons_inj_right z).mp he₁)) |>.trans hs.symm
    · have he₁' := congrArg (Multiset.count z) he₁
      have he₂' := congrArg (Multiset.count z) he₂
      change (z ::ₘ r).count z = (insertOption y' s).count z at he₁'
      change (z ::ₘ s).count z = (insertOption y'' r).count z at he₂'
      rw [Multiset.count_cons_self,count_insertOption_of_ne hsame] at he₁'
      cases y'' with
      | none => simp [insertOption] at he₂'; omega
      | some t =>
        simp only [insertOption,Option.elim_some,Multiset.count_cons_self,Multiset.count_cons] at he₂'
        split at he₂' <;> omega

/-- Two or more branches can be reconstructed from the set of cards when each
branch admits a shortening by one and all branch sizes are positive. -/
theorem eq_of_cards_eq {α : Type*} (size : α → ℕ) (trim : α → Option α → Prop)
    (hsize : ∀ x, 0 < size x) (hex : ∀ x, ∃ y, trim x y)
    (htrim : ∀ x y, trim x y → y.elim 0 size + 1 = size x)
    {a b : Multiset α} (ha : 2 ≤ a.card) (hb : 2 ≤ b.card)
    (he : cards trim a = cards trim b) : a = b := by
  classical
  let u := (a + b).toFinset
  have hu : u.Nonempty := by
    obtain ⟨x,hx⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < a.card)
    exact ⟨x,by simp [u,hx]⟩
  obtain ⟨x,hxu,hxmax⟩ := Finset.exists_max_image u size hu
  have hx : x ∈ a ∨ x ∈ b := by simpa [u] using hxu
  have hmax₁ : ∀ z ∈ a, size z ≤ size x := fun z hz => hxmax z (by simp [u,hz])
  have hmax₂ : ∀ z ∈ b, size z ≤ size x := fun z hz => hxmax z (by simp [u,hz])
  have transfer {m n : Multiset α} (hm : 2 ≤ m.card)
      (he' : cards trim m = cards trim n) (hn : ∀ z ∈ n, size z ≤ size x)
      (hmx : x ∈ m) : x ∈ n := by
    obtain ⟨c,hc,hxc⟩ := survives hex hm hmx
    have hcn : c ∈ cards trim n := he' ▸ hc
    have hbound := (count_on_card htrim hn (x := x) hcn).1
    exact Multiset.count_pos.mp ((Multiset.count_pos.mpr hxc).trans_le hbound)
  have hxa : x ∈ a := hx.elim id (transfer hb he.symm hmax₁)
  have hxb : x ∈ b := transfer ha he hmax₂ hxa
  obtain ⟨y,hy⟩ := hex x
  exact recovers_at hsize htrim hmax₁ hmax₂ hxa hxb he hy

end RootedBranchDeck

namespace FiniteRootedTree

open SimpleGraph TreeBranches

structure Tree where
  V : Type
  G : SimpleGraph V
  r : V
  connected : G.IsTree
  finite : Finite V

instance (T : Tree) : Finite T.V := T.finite

def Related (T U : Tree) : Prop := ∃ e : T.G ≃g U.G, e T.r = U.r

instance : Setoid Tree where
  r := Related
  iseqv := {
    refl := fun T => ⟨SimpleGraph.Iso.refl,rfl⟩
    symm := fun {T U} ⟨e,h⟩ => ⟨e.symm,e.symm_apply_eq.mpr h.symm⟩
    trans := fun {T U S} ⟨e,h⟩ ⟨f,h'⟩ => ⟨e.trans f,by simpa [h] using h'⟩ }

def Class := Quotient (inferInstance : Setoid Tree)

def ofTree (T : Tree) : Class := Quotient.mk' T

theorem ofTree_eq_iff {T U : Tree} : ofTree T = ofTree U ↔ Related T U :=
  Quotient.eq

noncomputable def order : Class → ℕ := Quotient.lift (fun T => Nat.card T.V)
  (fun _ _ ⟨e,_⟩ => Nat.card_congr e.toEquiv)

theorem order_pos (t : Class) : 0 < order t := by
  refine Quotient.inductionOn t fun T => ?_
  let _ : Nonempty T.V := ⟨T.r⟩
  exact Nat.card_pos

def IsLeaf (T : Tree) (l : T.V) : Prop := ∃! x, T.G.Adj l x

theorem unique_of_leaf {T : Tree} {l : T.V} (hl : IsLeaf T l) :
    ∀ a b, T.G.Adj l a → T.G.Adj l b → a = b := by
  obtain ⟨x,hx,hu⟩ := hl
  exact fun a b ha hb => (hu a ha).trans (hu b hb).symm

def leafCard (T : Tree) (l : T.V) (hn : T.r ≠ l) (hl : IsLeaf T l) : Tree where
  V := Deleted l
  G := cardAt T.G l
  r := newRoot hn
  finite := inferInstance
  connected := {
    isAcyclic := T.connected.isAcyclic.induce _
    connected := by
      have hreach := reachable_card_iff l (unique_of_leaf hl)
      let _ : Nonempty (Deleted l) := ⟨newRoot hn⟩
      exact ⟨fun x y => (hreach x y).mpr (T.connected.connected x.val y.val)⟩ }

theorem order_leafCard (T : Tree) (l : T.V) (hn : T.r ≠ l) (hl : IsLeaf T l) :
    order (ofTree (leafCard T l hn hl)) + 1 = order (ofTree T) := by
  classical
  change Nat.card ({l}ᶜ : Set T.V) + 1 = Nat.card T.V
  rw [Nat.card_coe_set_eq,Set.ncard_compl,Set.ncard_singleton]
  have : Nonempty T.V := ⟨l⟩
  have : 0 < Nat.card T.V := Nat.card_pos
  omega

def trim (t : Class) (card : Option Class) : Prop :=
  match card with
  | none => order t = 1
  | some u => ∃ (T : Tree) (l : T.V) (hn : T.r ≠ l) (hl : IsLeaf T l),
      ofTree T = t ∧ ofTree (leafCard T l hn hl) = u

theorem trim_size (t : Class) (c : Option Class) (h : trim t c) :
    c.elim 0 order + 1 = order t := by
  cases c with
  | none => exact h.symm
  | some u =>
    obtain ⟨T,l,hn,hl,rfl,rfl⟩ := h
    exact order_leafCard T l hn hl

theorem trim_exists (t : Class) : ∃ c, trim t c := by
  classical
  refine Quotient.inductionOn t fun T => ?_
  change ∃ c, trim (ofTree T) c
  by_cases hone : order (ofTree T) = 1
  · exact ⟨none,hone⟩
  · have hpos := order_pos (ofTree T)
    have htwo : 1 < Nat.card T.V := by
      change 1 < order (ofTree T)
      omega
    let _ : Fintype T.V := Fintype.ofFinite _
    let _ : Nontrivial T.V := Fintype.one_lt_card_iff_nontrivial.mp (by
      simpa only [Nat.card_eq_fintype_card] using htwo)
    obtain ⟨v,w,hn,hv,hw⟩ := T.connected.exists_ne_and_degree_eq_one
    by_cases he : T.r = v
    · have hr : T.r ≠ w := he.symm ▸ hn
      have hl : IsLeaf T w := (degree_eq_one_iff_existsUnique_adj).mp hw
      exact ⟨some (ofTree (leafCard T w hr hl)),T,w,hr,hl,rfl,rfl⟩
    · have hl : IsLeaf T v := (degree_eq_one_iff_existsUnique_adj).mp hv
      exact ⟨some (ofTree (leafCard T v he hl)),T,v,he,hl,rfl,rfl⟩

noncomputable abbrev branchTree (T : Tree) (C : Branch T.G T.r) : Tree where
  V := C.supp
  G := BranchGraph C
  r := attachment T.connected C
  connected := branch_isTree T.connected C
  finite := inferInstance

noncomputable def branchClass (T : Tree) (C : Branch T.G T.r) : Class := ofTree (branchTree T C)

noncomputable def branchMultiset (T : Tree) : Multiset Class :=
  letI := Fintype.ofFinite (Branch T.G T.r)
  (Finset.univ : Finset (Branch T.G T.r)).val.map (branchClass T)

private theorem count_branch {T : Tree} [DecidableEq Class] (t : Class) :
    (branchMultiset T).count t = Nat.card {C : Branch T.G T.r // branchClass T C = t} := by
  classical
  let _ : Fintype (Branch T.G T.r) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  unfold branchMultiset
  simp only [Multiset.count_map,← Finset.filter_val]
  apply congrArg Finset.card
  ext C
  simp [eq_comm]

theorem related_of_branchMultiset {T U : Tree} (h : branchMultiset T = branchMultiset U) :
    Related T U := by
  classical
  let f := branchClass T
  let g := branchClass U
  let e₀ (t : Class) : {C // f C = t} ≃ {D // g D = t} := by
    let _ : Fintype {C // f C = t} := Fintype.ofFinite _
    let _ : Fintype {D // g D = t} := Fintype.ofFinite _
    apply Fintype.equivOfCardEq
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,← count_branch t,← count_branch t,h]
  let e := Equiv.ofFiberEquiv e₀
  have he (C : Branch T.G T.r) : branchClass T C = branchClass U (e C) :=
    (Equiv.ofFiberEquiv_map e₀ C).symm
  have hmatch (C : Branch T.G T.r) : Related (branchTree T C) (branchTree U (e C)) :=
    ofTree_eq_iff.mp (he C)
  choose f' hf using hmatch
  refine ⟨combineBranches T.connected U.connected e f' hf,?_⟩
  simp [combineBranches,extendDeleted,Equiv.Set.sumCompl_symm_apply_of_mem (Set.mem_singleton T.r)]

theorem leaf_iff_card_neighbor (T : Tree) (x : T.V) :
    IsLeaf T x ↔ Nat.card (T.G.neighborSet x) = 1 := by
  classical
  let _ : Fintype T.V := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,degree_eq_one_iff_existsUnique_adj]
  rfl

private def branchNeighborEquiv (T : Tree) (C : Branch T.G T.r) (x : C.supp)
    (hx : x ≠ attachment T.connected C) :
    (BranchGraph C).neighborSet x ≃ T.G.neighborSet x.val.val where
  toFun z := ⟨z.val.val.val,z.property⟩
  invFun z := by
    have hz : z.val ≠ T.r := by
      intro h
      have hadj := (show T.G.Adj x.val.val z.val from z.property).symm
      rw [h] at hadj
      exact hx ((adj_iff_eq_attachment T.connected C x).mp hadj)
    let z' : Deleted T.r := ⟨z.val,hz⟩
    have hC := same_branch_of_adj (G := T.G) (x := x.val) (y := z') z.property
    exact ⟨⟨z',hC.symm.trans x.property⟩,z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem leaf_in_branch_iff (T : Tree) (C : Branch T.G T.r) (x : C.supp)
    (hx : x ≠ attachment T.connected C) :
    IsLeaf (branchTree T C) x ↔ IsLeaf T x.val.val := by
  rw [leaf_iff_card_neighbor,leaf_iff_card_neighbor,Nat.card_congr (branchNeighborEquiv T C x hx)]

theorem leaf_root_of_singleton_branch (T : Tree) (C : Branch T.G T.r)
    (hs : order (branchClass T C) = 1) :
    IsLeaf T (attachment T.connected C).val.val := by
  have hcard : Nat.card C.supp = 1 := hs
  have hs' : Subsingleton C.supp := (Nat.card_eq_one_iff_unique.mp hcard).1
  let x := attachment T.connected C
  refine ⟨T.r,(adj_attachment T.connected C).symm,?_⟩
  intro y hy
  by_contra hne
  let y' : Deleted T.r := ⟨y,hne⟩
  have hC := same_branch_of_adj (G := T.G) (x := x.val) (y := y') hy
  have he : (⟨y',hC.symm.trans x.property⟩ : C.supp) = x := Subsingleton.elim _ _
  exact (show T.G.Adj x.val.val y from hy).ne' (congrArg (fun a => a.val.val) he)

theorem singleton_branch_of_leaf_root (T : Tree) (C : Branch T.G T.r)
    (h : IsLeaf T (attachment T.connected C).val.val) :
    order (branchClass T C) = 1 := by
  classical
  let x := attachment T.connected C
  change Nat.card C.supp = 1
  by_contra hc
  have hpos : 0 < Nat.card C.supp := order_pos (branchClass T C)
  let _ : Fintype C.supp := Fintype.ofFinite _
  let _ : Nontrivial C.supp := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [← Nat.card_eq_fintype_card]
    omega)
  have hi : (BranchGraph C).IsIsolated x := by
    intro y ha
    have hh := unique_of_leaf h _ _ (show T.G.Adj x.val.val y.val.val from ha)
      (adj_attachment T.connected C).symm
    exact y.val.property hh
  exact ((branch_isTree T.connected C).connected.preconnected.not_isIsolated x) hi

theorem related_leafCard {T U : Tree} (e : T.G ≃g U.G) (he : e T.r = U.r)
    (l : T.V) (hn : T.r ≠ l) (hl : IsLeaf T l) :
    ∃ (hn' : U.r ≠ e l) (hl' : IsLeaf U (e l)),
      Related (leafCard T l hn hl) (leafCard U (e l) hn' hl') := by
  have hn' : U.r ≠ e l := he ▸ e.injective.ne hn
  have hl' : IsLeaf U (e l) := by
    rw [leaf_iff_card_neighbor] at hl ⊢
    rwa [← Nat.card_congr (e.mapNeighborSet l)]
  let f : cardAt T.G l ≃g cardAt U.G (e l) :=
    e.induce (by
      refine ⟨fun x hx => e.injective.ne (show x ≠ l from hx), e.injective.injOn, ?_⟩
      intro y hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      intro h
      have hh : e.symm y = l := Set.mem_singleton_iff.mp h
      have hy' : y = e l := (e.apply_symm_apply y).symm.trans (congrArg e hh)
      exact hy (Set.mem_singleton_iff.mpr hy'))
  exact ⟨hn',hl',f,Subtype.ext he⟩

theorem trim_some_ofTree_iff (T : Tree) (t : Class) :
    trim (ofTree T) (some t) ↔
      ∃ (l : T.V) (hn : T.r ≠ l) (hl : IsLeaf T l), ofTree (leafCard T l hn hl) = t := by
  constructor
  · rintro ⟨U,x,hx,hl,hU,hcard⟩
    obtain ⟨e,he⟩ := ofTree_eq_iff.mp hU
    obtain ⟨hn',hl',hh⟩ := related_leafCard e he x hx hl
    exact ⟨e x,hn',hl',(ofTree_eq_iff.mpr hh).symm.trans hcard⟩
  · rintro ⟨l,hn,hl,he⟩
    exact ⟨T,l,hn,hl,rfl,he⟩

private noncomputable def enum {I A : Type*} [Finite I] (f : I → A) : Multiset A :=
  let _ : Fintype I := Fintype.ofFinite _
  (Finset.univ : Finset I).val.map f

private theorem enum_congr {I J A : Type*} [Finite I] [Finite J]
    (e : I ≃ J) (f : I → A) (g : J → A) (he : ∀ x, f x = g (e x)) :
    enum f = enum g := by
  classical
  unfold enum
  exact Multiset.map_eq_map_of_bij_of_nodup f g (Finset.nodup _) (Finset.nodup _)
    (fun x _ => e x) (by simp) (fun _ _ _ _ hh => e.injective hh)
    (fun y _ => ⟨e.symm y, by simp, e.apply_symm_apply y⟩) (fun x _ => he x)

private theorem enum_split {I A : Type*} [Finite I] (f : I → A) (i : I) :
    enum f = f i ::ₘ enum (fun x : {x // x ≠ i} => f x.val) := by
  classical
  let _ : Fintype I := Fintype.ofFinite _
  have he : (Finset.univ.erase i).val.map f = enum (fun x : {x // x ≠ i} => f x.val) := by
    unfold enum
    apply Multiset.map_eq_map_of_bij_of_nodup f _ (Finset.nodup _) (Finset.nodup _)
      (fun x hx => ⟨x,(Finset.mem_erase.mp (show x ∈ Finset.univ.erase i from hx)).1⟩)
    · simp
    · intro _ _ _ _ h
      exact congrArg Subtype.val h
    · rintro ⟨x,hx⟩ _
      exact ⟨x,show x ∈ Finset.univ.erase i from by simp [hx],rfl⟩
    · intros
      rfl
  change (Finset.univ : Finset I).val.map f = _
  rw [← he,← Multiset.map_cons]
  congr 1
  rw [Finset.erase_val]
  exact (Multiset.cons_erase (show i ∈ (Finset.univ : Finset I).val from Finset.mem_univ i)).symm

private def pointInBranch {T : Tree} {l : T.V} (hn : T.r ≠ l) :
    ((cardAt T.G T.r).connectedComponentMk (removedInBranch hn)).supp :=
  ⟨removedInBranch hn,rfl⟩

private noncomputable def setInduceIso {V : Type*} (G : SimpleGraph V)
    {U W : Set V} (h : U = W) : G.induce U ≃g G.induce W :=
  {toEquiv := Equiv.setCongr h, map_rel_iff' := Iff.rfl}

noncomputable def selectedTrim (T : Tree) (C : Branch T.G T.r) (p : C.supp)
    (hl : IsLeaf T p.val.val) : Option Class := by
  classical
  exact if h : (branchTree T C).r ≠ p then
    some (ofTree (leafCard (branchTree T C) p h ((leaf_in_branch_iff T C p h.symm).mpr hl)))
  else none

/-- The graph leaf card trims exactly the branch containing the removed leaf. -/
theorem branchMultiset_leaf_replace (T : Tree) (l : T.V) (hn : T.r ≠ l)
    (hl : IsLeaf T l) :
    let C := (cardAt T.G T.r).connectedComponentMk (removedInBranch hn)
    ∃ m, branchMultiset T = branchClass T C ::ₘ m ∧
      branchMultiset (leafCard T l hn hl) =
        RootedBranchDeck.insertOption (selectedTrim T C (pointInBranch hn) hl) m := by
  classical
  let U := leafCard T l hn hl
  let D := (cardAt T.G T.r).connectedComponentMk (removedInBranch hn)
  let e := branchOfLeafCardEquiv (G := T.G) hn (unique_of_leaf hl)
  let f (C : Branch T.G T.r) := branchClass T C
  let remains (C : Branch T.G T.r) := ∃ x : C.supp, x.val.val ≠ l
  let g (C : {C : Branch T.G T.r // remains C}) := branchClass U (e.symm C)
  have hg : branchMultiset U = enum g := by
    exact enum_congr e (branchClass U) g (fun C => by simp [g])
  have seen (C : Branch T.G T.r) (x : C.supp) (hx : x.val.val = l) : C = D := by
    have hex : x.val = removedInBranch hn := Subtype.ext hx
    exact (hex ▸ x.property).symm
  have exists_point (C : {C : Branch T.G T.r // C ≠ D}) : remains C := by
    obtain ⟨x,hx⟩ := C.val.nonempty_supp
    exact ⟨⟨x,hx⟩,fun hh => C.property (seen C ⟨x,hx⟩ hh)⟩
  have branchUnchanged (C : Branch T.G T.r) (hC : C ≠ D) (hp : remains C) :
      g ⟨C,hp⟩ = f C := by
    apply ofTree_eq_iff.mpr
    let C' := e.symm ⟨C,hp⟩
    have hindex : survivingBranch hn C' = C := congrArg Subtype.val (e.apply_symm_apply ⟨C,hp⟩)
    have hall : ({x | x.val.val ≠ l} : Set C.supp) = Set.univ := by
      ext x
      exact iff_of_true (fun he => hC (seen C x he)) (Set.mem_univ x)
    have q : ∃ (iso : BranchGraph C' ≃g (BranchGraph C).induce {x | x.val.val ≠ l}),
        (iso (attachment U.connected C')).val = attachment T.connected C := by
      rw [← hindex]
      exact ⟨branchOfLeafCardIso hn (unique_of_leaf hl) C',
        branchOfLeafCardIso_root hn (unique_of_leaf hl) T.connected U.connected C'⟩
    obtain ⟨iso,hi⟩ := q
    refine ⟨iso.trans ((setInduceIso (BranchGraph C) hall).trans (SimpleGraph.induceUnivIso _)),?_⟩
    exact hi
  let lower := enum (fun C : {C : Branch T.G T.r // C ≠ D} => f C.val)
  have hsplit : branchMultiset T = f D ::ₘ lower := enum_split f D
  by_cases hD : remains D
  · let D' : {C : Branch T.G T.r // remains C} := ⟨D,hD⟩
    let e' : {C : {C : Branch T.G T.r // remains C} // C ≠ D'} ≃
        {C : Branch T.G T.r // C ≠ D} := {
      toFun := fun C => ⟨C.val.val,fun h => C.property (Subtype.ext h)⟩
      invFun := fun C => ⟨⟨C.val,exists_point C⟩,fun h => C.property (congrArg Subtype.val h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have henum : enum (fun C : {C // C ≠ D'} => g C.val) = lower :=
      enum_congr e' _ _ (fun C => branchUnchanged C.val.val (e' C).property C.val.property)
    have htrim : selectedTrim T D (pointInBranch hn) hl = some (g D') := by
      let p : D.supp := pointInBranch hn
      have hp : (branchTree T D).r ≠ p := by
        intro he
        have hpos : 1 < Nat.card D.supp := by
          obtain ⟨z,hz⟩ := hD
          let _ : Nontrivial D.supp := ⟨⟨z,p,fun h => hz (congrArg (fun v => v.val.val) h)⟩⟩
          let _ : Fintype D.supp := Fintype.ofFinite _
          rw [Nat.card_eq_fintype_card]
          exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
        have hleaf : IsLeaf T (attachment T.connected D).val.val := by
          have hq : (attachment T.connected D).val.val = l :=
            congrArg (fun v : D.supp => v.val.val) he
          rwa [hq]
        have ha := singleton_branch_of_leaf_root T D hleaf
        change Nat.card D.supp = 1 at ha
        omega
      have hpl : IsLeaf (branchTree T D) p := (leaf_in_branch_iff T D p hp.symm).mpr hl
      unfold selectedTrim
      rw [dif_pos hp]
      apply congrArg some
      apply ofTree_eq_iff.mpr
      let Q := e.symm D'
      have hi : survivingBranch hn Q = D := congrArg Subtype.val (e.apply_symm_apply D')
      have hsets : ({x | x.val.val ≠ l} : Set D.supp) = {p}ᶜ := by
        ext x
        change x.val.val ≠ l ↔ x ≠ p
        exact not_congr ⟨fun he => Subtype.ext (Subtype.ext he),
          fun he => congrArg (fun v => v.val.val) he⟩
      have q : ∃ (iso : BranchGraph Q ≃g (BranchGraph D).induce {x | x.val.val ≠ l}),
          (iso (attachment U.connected Q)).val = attachment T.connected D := by
        rw [← hi]
        exact ⟨branchOfLeafCardIso hn (unique_of_leaf hl) Q,
          branchOfLeafCardIso_root hn (unique_of_leaf hl) T.connected U.connected Q⟩
      obtain ⟨iso,hiso⟩ := q
      let iso' := iso.trans (setInduceIso _ hsets)
      exact ⟨iso'.symm,iso'.symm_apply_eq.mpr (Subtype.ext hiso.symm)⟩
    exact ⟨lower,hsplit,by rw [htrim,hg,enum_split g D',henum]; rfl⟩
  · let e' : {C : Branch T.G T.r // remains C} ≃ {C : Branch T.G T.r // C ≠ D} := {
      toFun := fun C => ⟨C.val,fun h => hD (h ▸ C.property)⟩
      invFun := fun C => ⟨C.val,exists_point C⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have henum : enum g = lower := enum_congr e' _ _ (fun C =>
      branchUnchanged C.val (e' C).property C.property)
    have hr : (branchTree T D).r = pointInBranch hn := by
      apply Subtype.ext
      apply Subtype.ext
      exact not_not.mp (fun hh => hD ⟨attachment T.connected D,hh⟩)
    have ht : selectedTrim T D (pointInBranch hn) hl = none := by
      unfold selectedTrim
      exact dif_neg (not_not.mpr hr)
    exact ⟨lower,hsplit,by rw [ht]; exact hg.trans henum⟩

private theorem selectedTrim_is_trim (T : Tree) (C : Branch T.G T.r) (p : C.supp)
    (hl : IsLeaf T p.val.val) : trim (branchClass T C) (selectedTrim T C p hl) := by
  classical
  by_cases h : (branchTree T C).r ≠ p
  · rw [selectedTrim,dif_pos h]
    exact (trim_some_ofTree_iff _ _).mpr ⟨p,h,_,rfl⟩
  · rw [selectedTrim,dif_neg h]
    have hh : p = attachment T.connected C := (not_not.mp h).symm
    subst p
    exact singleton_branch_of_leaf_root T C hl

private theorem branchMultiset_replace (T : Tree) (C : Branch T.G T.r) (p : C.supp)
    (hl : IsLeaf T p.val.val) :
    ∃ m, branchMultiset T = branchClass T C ::ₘ m ∧
      branchMultiset (leafCard T p.val.val (Ne.symm p.val.property) hl) =
        RootedBranchDeck.insertOption (selectedTrim T C p hl) m := by
  rcases p with ⟨x,hx⟩
  change (cardAt T.G T.r).connectedComponentMk x = C at hx
  subst C
  exact branchMultiset_leaf_replace T x.val (Ne.symm x.property) hl

theorem cards_branchMultiset (T : Tree) :
    RootedBranchDeck.cards trim (branchMultiset T) =
      {m | ∃ (l : T.V) (h : T.r ≠ l) (hl : IsLeaf T l),
        branchMultiset (leafCard T l h hl) = m} := by
  classical
  ext m
  constructor
  · rintro ⟨x,next,rest,hx,htrim,hm⟩
    have hmem : x ∈ branchMultiset T := hx ▸ by simp
    unfold branchMultiset at hmem
    obtain ⟨C,_,hC⟩ := Multiset.mem_map.mp hmem
    subst x
    have make (p : C.supp) (hl : IsLeaf T p.val.val)
        (hnext : selectedTrim T C p hl = next) :
        ∃ (l : T.V) (h : T.r ≠ l) (hl : IsLeaf T l),
          branchMultiset (leafCard T l h hl) = m := by
      obtain ⟨r,hr,he⟩ := branchMultiset_replace T C p hl
      have hr' : r = rest := (Multiset.cons_inj_right _).mp (hr.symm.trans hx)
      refine ⟨p.val.val,Ne.symm p.val.property,hl,?_⟩
      rw [he,hnext,hr',← hm]
    cases next with
    | none =>
      let p := attachment T.connected C
      have hp := leaf_root_of_singleton_branch T C htrim
      exact make p hp (by simp [selectedTrim,p])
    | some t =>
      obtain ⟨p,hp,hl,hcard⟩ := (trim_some_ofTree_iff _ _).mp htrim
      let hl' := (leaf_in_branch_iff T C p hp.symm).mp hl
      exact make p hl' (by simp [selectedTrim,hp,hcard])
  · rintro ⟨l,hn,hl,rfl⟩
    let D := (cardAt T.G T.r).connectedComponentMk (removedInBranch hn)
    let p : D.supp := pointInBranch hn
    obtain ⟨r,hsrc,hcard⟩ := branchMultiset_leaf_replace T l hn hl
    exact ⟨branchClass T D,selectedTrim T D p hl,r,hsrc,selectedTrim_is_trim T D p hl,hcard⟩

private def deletedIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {r : V} {s : W}
    (e : G ≃g H) (he : e r = s) : cardAt G r ≃g cardAt H s where
  toEquiv := {
    toFun := fun x => ⟨e x.val,by
      intro hx
      exact x.property (e.injective ((Set.mem_singleton_iff.mp hx).trans he.symm))⟩
    invFun := fun y => ⟨e.symm y.val,by
      intro hy
      exact y.property (Set.mem_singleton_iff.mpr
        ((e.apply_symm_apply y.val).symm.trans ((congrArg e (Set.mem_singleton_iff.mp hy)).trans he)))⟩
    left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
    right_inv := fun y => Subtype.ext (e.apply_symm_apply y.val) }
  map_rel_iff' := e.map_rel_iff

theorem branchMultiset_related {T U : Tree} (h : Related T U) :
    branchMultiset T = branchMultiset U := by
  obtain ⟨e,hr⟩ := h
  let f := deletedIso e hr
  apply enum_congr f.connectedComponentEquiv
  intro C
  apply ofTree_eq_iff.mpr
  let q := restrictComponentIso f C
  refine ⟨q,?_⟩
  apply (adj_iff_eq_attachment U.connected _ _).mp
  change U.G.Adj U.r (e (attachment T.connected C).val.val)
  rw [← hr]
  exact e.map_adj_iff.mpr (adj_attachment T.connected C)

def rootedCards (T : Tree) : Set Class :=
  {t | ∃ (x : T.V) (h : T.r ≠ x) (hl : IsLeaf T x),
        ofTree (leafCard T x h hl) = t}

/-- A tree whose root has at least two branches is reconstructed when the
root is identified in all its non-root leaf cards. -/
theorem related_of_rootedCards_eq {T U : Tree}
    (hT : 2 ≤ (branchMultiset T).card) (hU : 2 ≤ (branchMultiset U).card)
    (h : rootedCards T = rootedCards U) : Related T U := by
  apply related_of_branchMultiset
  apply RootedBranchDeck.eq_of_cards_eq order trim order_pos trim_exists trim_size hT hU
  rw [cards_branchMultiset,cards_branchMultiset]
  ext m
  constructor
  · rintro ⟨x,hx,hl,rfl⟩
    have hc : ofTree (leafCard T x hx hl) ∈ rootedCards T := ⟨x,hx,hl,rfl⟩
    obtain ⟨y,hy,hl',he⟩ := (show _ ∈ rootedCards U from h ▸ hc)
    exact ⟨y,hy,hl',branchMultiset_related (ofTree_eq_iff.mp he)⟩
  · rintro ⟨y,hy,hl,rfl⟩
    have hc : ofTree (leafCard U y hy hl) ∈ rootedCards U := ⟨y,hy,hl,rfl⟩
    obtain ⟨x,hx,hl',he⟩ := (show _ ∈ rootedCards T from h.symm ▸ hc)
    exact ⟨x,hx,hl',branchMultiset_related (ofTree_eq_iff.mp he)⟩

end FiniteRootedTree

/-
Counting induced copies from vertex-deleted cards

Kelly's double count identifies pairs of an induced embedding and an omitted
vertex with induced embeddings into cards. See Lemma 1 of Paul J. Kelly,
[A congruence theorem for trees](https://msp.org/pjm/1957/7-1/pjm-v7-n1-p14-p.pdf).
-/

open scoped BigOperators

namespace TreeReconstruction

open ReconstructionConjecture SimpleGraph

private def lower {A V : Type*} {F : SimpleGraph A} {G : SimpleGraph V} (s : Set V)
    (f : F ↪g G) (hf : ∀ a, f a ∈ s) : F ↪g G.induce s where
  toFun a := ⟨f a,hf a⟩
  inj' := fun _ _ h => f.injective (congrArg Subtype.val h)
  map_rel_iff' := f.map_rel_iff

private def embeddingsIntoCard {A V : Type*} (F : SimpleGraph A) (G : SimpleGraph V)
    (v : V) : (F ↪g G.induce {v}ᶜ) ≃ {f : F ↪g G // v ∉ Set.range f} where
  toFun f := ⟨(SimpleGraph.Embedding.induce _).comp f,by
    rintro ⟨a,ha⟩
    exact (f a).property (by simpa using ha)⟩
  invFun f := lower ({v}ᶜ : Set V) f.val (fun a => by
    intro h
    exact f.property ⟨a,by simpa using h⟩)
  left_inv f := by
    ext a
    rfl
  right_inv f := by
    apply Subtype.ext
    ext a
    rfl

private def flipOmission {A V : Type*} (F : SimpleGraph A) (G : SimpleGraph V) :
    (Σ v : V, {f : F ↪g G // v ∉ Set.range f}) ≃
      Σ f : F ↪g G, {v : V // v ∉ Set.range f} where
  toFun p := ⟨p.2.val,⟨p.1,p.2.property⟩⟩
  invFun p := ⟨p.2.val,⟨p.1,p.2.property⟩⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

private def countEquiv {A V W : Type*} (F : SimpleGraph A) {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : (F ↪g G) ≃ (F ↪g H) where
  toFun f := f.trans e.toRelEmbedding
  invFun f := f.trans e.symm.toRelEmbedding
  left_inv f := by ext a; exact e.symm_apply_apply (f a)
  right_inv f := by ext a; exact e.apply_symm_apply (f a)

private theorem cardIncidence {A V : Type*} [Fintype A] [Fintype V]
    (F : SimpleGraph A) (G : SimpleGraph V) :
    Nat.card (Σ v : V, F ↪g G.induce {v}ᶜ) =
      Nat.card (F ↪g G) * (Fintype.card V-Fintype.card A) := by
  classical
  let _ : Fintype (F ↪g G) := Fintype.ofFinite _
  have he := (Equiv.sigmaCongrRight (embeddingsIntoCard F G)).trans (flipOmission F G)
  rw [Nat.card_congr he,Nat.card_sigma]
  have hv (f : F ↪g G) : Nat.card {v : V // v ∉ Set.range f} =
      Fintype.card V-Fintype.card A := by
    change Nat.card ((Set.range f)ᶜ : Set V) = _
    rw [Nat.card_coe_set_eq,Set.ncard_compl,Set.ncard_range_of_injective f.injective]
    simp
  simp only [hv,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]

/-- A proper induced pattern has the same embedding count in hypomorphic graphs. -/
theorem inducedEmbedding_card_eq {A V W : Type*} [Fintype A] [Fintype V] [Fintype W]
    (F : SimpleGraph A) {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Hypomorphic G H) (hsmall : Fintype.card A < Fintype.card V) :
    Nat.card (F ↪g G) = Nat.card (F ↪g H) := by
  classical
  have hcard := h.card_eq
  obtain ⟨σ,hσ⟩ := h
  let e : (Σ v : V, F ↪g G.induce {v}ᶜ) ≃ (Σ w : W, F ↪g H.induce {w}ᶜ) :=
    Equiv.sigmaCongr σ (fun v => countEquiv F (hσ v).some)
  have hsame := Nat.card_congr e
  rw [cardIncidence F G,cardIncidence F H,← hcard] at hsame
  exact mul_right_cancel₀ (Nat.sub_ne_zero_of_lt hsmall) hsame

private def edgeEmbedding {V : Type*} (G : SimpleGraph V) :
    ((⊤ : SimpleGraph (Fin 2)) ↪g G) ≃ G.Dart where
  toFun f := ⟨(f 0,f 1), f.map_adj_iff.mpr (by decide)⟩
  invFun d := {
    toFun := ![d.fst,d.snd]
    inj' := by
      intro i j h
      fin_cases i <;> fin_cases j
      · rfl
      · exact (d.fst_ne_snd h).elim
      · exact (d.snd_ne_fst h).elim
      · rfl
    map_rel_iff' := by
      intro i j
      fin_cases i <;> fin_cases j
      · simp
      · exact iff_of_true d.adj (by decide)
      · exact iff_of_true d.adj.symm (by decide)
      · simp
  }
  left_inv f := by
    ext i
    fin_cases i <;> rfl
  right_inv d := by
    apply SimpleGraph.Dart.ext
    rfl

theorem edge_card_eq {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} (h : Hypomorphic G H) (hV : 3 ≤ Fintype.card V) :
    Nat.card G.edgeSet = Nat.card H.edgeSet := by
  classical
  have he := inducedEmbedding_card_eq (⊤ : SimpleGraph (Fin 2)) h (by simp; omega)
  rw [Nat.card_congr (edgeEmbedding G),Nat.card_congr (edgeEmbedding H)] at he
  simp only [Nat.card_eq_fintype_card]
  simp only [Nat.card_eq_fintype_card,SimpleGraph.dart_card_eq_twice_card_edges] at he
  rw [SimpleGraph.card_edgeSet,SimpleGraph.card_edgeSet]
  omega

private theorem reachable_of_card {V : Type*} {G : SimpleGraph V} {v x y : V}
    (hc : (G.induce {v}ᶜ).Connected) (hx : x ≠ v) (hy : y ≠ v) : G.Reachable x y := by
  let x' : ({v}ᶜ : Set V) := ⟨x,by simpa using hx⟩
  let y' : ({v}ᶜ : Set V) := ⟨y,by simpa using hy⟩
  exact (hc x' y').map (SimpleGraph.Embedding.induce _).toHom

private theorem connected_of_two_cards {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hV : 3 ≤ Fintype.card V) {v w : V} (hvw : v ≠ w) (hv : (G.induce {v}ᶜ).Connected)
    (hw : (G.induce {w}ᶜ).Connected) : G.Connected := by
  classical
  obtain ⟨x,hxv,hxw⟩ : ∃ x : V, x ≠ v ∧ x ≠ w := by
    by_contra! he
    have hsub : (Finset.univ : Finset V) ⊆ {v,w} := by
      intro y _
      by_cases hy : y = v
      · exact Finset.mem_insert.mpr (Or.inl hy)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (he y hy)))
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ,Finset.card_pair hvw] at hc
    omega
  apply (SimpleGraph.connected_iff_exists_forall_reachable (G := G)).mpr
  refine ⟨x,fun y => ?_⟩
  by_cases hy : y = v
  · subst y
    exact reachable_of_card hw hxw hvw
  · exact reachable_of_card hv hxv hy

/-- At least two connected cards recognize connectedness for a tree. Together
with Kelly's count for edges this recognizes the class of trees. -/
theorem tree_of_hypomorphic {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (hV : 3 ≤ Fintype.card V) (hG : G.IsTree)
    (h : Hypomorphic G H) : H.IsTree := by
  classical
  have hcard := h.card_eq
  have he := edge_card_eq h hV
  have hVNontrivial : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v,w,hvw,hv,hw⟩ := hG.exists_ne_and_degree_eq_one
  obtain ⟨σ,hσ⟩ := h
  have hConnect (x : V) (hx : G.degree x = 1) :
      (H.induce {σ x}ᶜ).Connected :=
    (hG.connected.induce_compl_singleton_of_degree_eq_one hx).map
      (hσ x).some.toHom (hσ x).some.surjective
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨connected_of_two_cards (by omega) (σ.injective.ne hvw) (hConnect v hv) (hConnect w hw),?_⟩
  have hsize := (SimpleGraph.isTree_iff_connected_and_card.mp hG).2
  rw [← he]
  simpa only [Nat.card_eq_fintype_card, ← hcard] using hsize

private theorem deletion_edge_count {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    Nat.card (G.induce {v}ᶜ).edgeSet + Nat.card (G.incidenceSet v) = Nat.card G.edgeSet := by
  classical
  let f : ({v}ᶜ : Set V) ↪ V := Function.Embedding.subtype _
  have he : ((G.induce {v}ᶜ).map f).edgeSet = G.edgeSet \ G.incidenceSet v := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.map_adj, Set.mem_sdiff,
        SimpleGraph.mk'_mem_incidenceSet_iff, SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨x',y',hadj,rfl,rfl⟩
        exact ⟨hadj, fun h => h.2.elim
          (fun h => x'.property (by simpa using (show v = x'.val from h).symm))
          (fun h => y'.property (by simpa using (show v = y'.val from h).symm))⟩
      · rintro ⟨hadj,h⟩
        refine ⟨⟨x,by simpa using (fun h' : x = v => h ⟨hadj,Or.inl h'.symm⟩)⟩,
          ⟨y,by simpa using (fun h' : y = v => h ⟨hadj,Or.inr h'.symm⟩)⟩, hadj, rfl, rfl⟩
  have hcard : Nat.card ((G.induce {v}ᶜ).map f).edgeSet = Nat.card (G.induce {v}ᶜ).edgeSet := by
    simp only [Nat.card_eq_fintype_card]
    rw [SimpleGraph.card_edgeSet, SimpleGraph.card_edgeSet]
    exact SimpleGraph.card_edgeFinset_map f _
  rw [← hcard, he]
  simp only [Nat.card_coe_set_eq]
  exact Set.ncard_sdiff_add_ncard_of_subset (G.incidenceSet_subset v)

/-- Each vertex degree equals the degree at the matching vertex in a
hypomorphism of graphs on at least three vertices. -/
theorem degree_preserving_hypomorphism {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (hV : 3 ≤ Fintype.card V)
    (h : Hypomorphic G H) :
    ∃ σ : V ≃ W,
      (∀ v, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) ∧
      ∀ v, Nat.card (G.neighborSet v) = Nat.card (H.neighborSet (σ v)) := by
  classical
  have he := edge_card_eq h hV
  obtain ⟨σ,hσ⟩ := h
  refine ⟨σ,hσ,fun v => ?_⟩
  have h₁ := deletion_edge_count G v
  have h₂ := deletion_edge_count H (σ v)
  have h₃ : Nat.card (G.induce {v}ᶜ).edgeSet = Nat.card (H.induce {σ v}ᶜ).edgeSet := by
    simp only [Nat.card_eq_fintype_card]
    rw [SimpleGraph.card_edgeSet, SimpleGraph.card_edgeSet]
    exact (hσ v).some.card_edgeFinset_eq
  rw [Nat.card_congr (G.incidenceSetEquivNeighborSet v)] at h₁
  rw [Nat.card_congr (H.incidenceSetEquivNeighborSet (σ v))] at h₂
  omega

private theorem Walk.exists_exit {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (s : Set V) (hu : u ∈ s) (hv : v ∉ s) :
    ∃ x ∈ s, ∃ y ∉ s, G.Adj x y := by
  classical
  induction p with
  | nil => exact (hv hu).elim
  | @cons x y z h p ih =>
      by_cases hy : y ∈ s
      · exact ih hy hv
      · exact ⟨x, hu, y, hy, h⟩

private theorem path_of_degree_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsTree) (hdeg : ∀ v, Nat.card (G.neighborSet v) ≤ 2) :
    Nonempty (pathGraph (Fintype.card V) ≃g G) := by
  classical
  have := hG.nonempty
  obtain ⟨u,v,p,hp,hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have hspan : p.toSubgraph.IsSpanning := by
    intro z
    rw [p.mem_verts_toSubgraph]
    by_contra hz
    obtain ⟨q⟩ := hG.connected u z
    obtain ⟨x,hx,y,hy,hxy⟩ := Walk.exists_exit q {x | x ∈ p.support} p.start_mem_support hz
    change y ∉ p.support at hy
    obtain ⟨i,hi,hle⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    by_cases hi0 : i = 0
    · have hxu : x = u := by simpa [hi0] using hi.symm
      have hadj : G.Adj y u := hxu ▸ hxy.symm
      have hl := hmax _ _ _ (hp.cons hy (h := hadj))
      simp only [Walk.length_cons] at hl
      omega
    by_cases hie : i = p.length
    · have hxv : x = v := by simpa [hie] using hi.symm
      have hadj : G.Adj v y := hxv ▸ hxy
      have hl := hmax _ _ _ (hp.concat hy hadj)
      simp only [Walk.length_concat] at hl
      omega
    let x₀ := p.getVert (i-1)
    let x₁ := p.getVert (i+1)
    have hx₀ : G.Adj x x₀ := by
      have ha := p.adj_getVert_succ (i := i-1) (by omega)
      rwa [show i-1+1 = i by omega,hi,adj_comm] at ha
    have hx₁ : G.Adj x x₁ := by
      have ha := p.adj_getVert_succ (i := i) (by omega)
      rwa [hi] at ha
    have hne : x₀ ≠ x₁ := by
      intro heq
      have heq' : i-1 = i+1 := hp.getVert_injOn (by simp; omega) (by simp; omega) heq
      omega
    have hy₀ : y ≠ x₀ := fun heq => hy (heq ▸ p.getVert_mem_support (i-1))
    have hy₁ : y ≠ x₁ := fun heq => hy (heq ▸ p.getVert_mem_support (i+1))
    have hsub : ({x₀,x₁,y} : Finset V) ⊆ G.neighborFinset x := by
      intro t ht
      simp only [Finset.mem_insert,Finset.mem_singleton] at ht
      rcases ht with (rfl | rfl | rfl) <;> simpa
    have hd := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hne,hy₀.symm]),
      Finset.card_pair hy₁.symm,SimpleGraph.card_neighborFinset_eq_degree] at hd
    have hd' := hdeg x
    rw [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] at hd'
    omega
  let e : p.toSubgraph.coe ≃g p.toSubgraph.spanningCoe :=
    { toEquiv := {
        toFun := Subtype.val
        invFun := fun z => ⟨z,hspan z⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      map_rel_iff' := Iff.rfl }
  have hsConn : p.toSubgraph.spanningCoe.Connected :=
    e.connected_iff.mp p.toSubgraph_connected.coe
  have hsLE : p.toSubgraph.spanningCoe ≤ G := fun _ _ h => h.adj_sub
  have hsTree := (hG.connected.maximal_le_isAcyclic_iff_isTree hsLE).mpr
    ⟨hsConn,hG.isAcyclic.anti hsLE⟩
  have hs : p.toSubgraph.spanningCoe = G := (hsTree.2 ⟨le_rfl,hG.isAcyclic⟩ hsLE).antisymm' hsLE
  let eG : p.toSubgraph.coe ≃g G :=
    cast (congrArg (fun S : SimpleGraph V => p.toSubgraph.coe ≃g S) hs) e
  let ep : pathGraph (p.length+1) ≃g G := hp.pathGraphIsoToSubgraph.trans eG
  have hsize : p.length+1 = Fintype.card V := by simpa using Fintype.card_congr ep.toEquiv
  exact ⟨hsize ▸ ep⟩

/-- A path is reconstructible from its vertex-deleted deck. -/
theorem path_reconstruction {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (hV : 3 ≤ Fintype.card V) (hG : G.IsTree)
    (hdeg : ∀ v, Nat.card (G.neighborSet v) ≤ 2) (h : Hypomorphic G H) :
    Nonempty (G ≃g H) := by
  obtain ⟨σ,hσ,hσdeg⟩ := degree_preserving_hypomorphism hV h
  have hdeg' (w : W) : Nat.card (H.neighborSet w) ≤ 2 := by
    obtain ⟨v,rfl⟩ := σ.surjective w
    rw [← hσdeg v]
    exact hdeg v
  obtain ⟨e⟩ := path_of_degree_le_two hG hdeg
  obtain ⟨e'⟩ := path_of_degree_le_two (tree_of_hypomorphic hV hG h) hdeg'
  have he : Fintype.card V = Fintype.card W := h.card_eq
  exact ⟨e.symm.trans (he.symm ▸ e')⟩

end TreeReconstruction

namespace TreeCentroid

open TreeBranches SimpleGraph

section

variable {V : Type*} {G : SimpleGraph V} {r : V}

def branchVerts (C : Branch G r) : Set V := Set.range (fun x : C.supp => x.val.val)

theorem card_branchVerts [Finite V] (C : Branch G r) :
    (branchVerts C).ncard = Nat.card C.supp :=
  Set.ncard_range_of_injective (fun _ _ h => Subtype.ext (Subtype.ext h))

theorem root_not_branchVerts (C : Branch G r) : r ∉ branchVerts C := by
  rintro ⟨x,hx⟩
  exact x.val.property hx

def branchInclusion (C : Branch G r) : BranchGraph C ↪g G :=
  (SimpleGraph.Embedding.induce ({r}ᶜ : Set V)).comp (SimpleGraph.Embedding.induce C.supp)

theorem outside_reachable_after_delete (hG : G.IsTree) (C : Branch G r) (z : C.supp)
    (x : V) (hx : x ∉ branchVerts C) :
    ∃ (hr : r ≠ z.val.val) (hh : x ≠ z.val.val),
      (cardAt G z.val.val).Reachable ⟨r,hr⟩ ⟨x,hh⟩ := by
  have hr : r ≠ z.val.val := Ne.symm z.val.property
  have hh : x ≠ z.val.val := fun h => hx ⟨z,h.symm⟩
  refine ⟨hr,hh,?_⟩
  by_cases hxr : x = r
  · subst x
    rfl
  let x' : Deleted r := ⟨x,hxr⟩
  let D := (cardAt G r).connectedComponentMk x'
  have hDC : D ≠ C := by
    intro he
    exact hx ⟨⟨x',he⟩,rfl⟩
  let q := (branch_isTree hG D).connected.preconnected (attachment hG D) ⟨x',rfl⟩
  obtain ⟨w⟩ := q
  let w' := w.map (branchInclusion D).toHom
  let p : G.Walk r x := w'.cons (adj_attachment hG D)
  have hsupport : p.support = r :: w'.support := rfl
  have avoids : ∀ t ∈ p.support, t ∈ ({z.val.val}ᶜ : Set V) := by
    intro t ht he
    have hm : z.val.val ∈ p.support := (show t = z.val.val from he) ▸ ht
    rw [hsupport,List.mem_cons] at hm
    rcases hm with (hm | hm)
    · exact z.val.property hm
    · rw [Walk.support_map] at hm
      obtain ⟨v,_,hv⟩ := List.mem_map.mp hm
      have hv' : v.val = z.val := Subtype.ext hv
      have hD : (cardAt G r).connectedComponentMk v.val = D := v.property
      rw [hv'] at hD
      exact hDC (hD.symm.trans z.property)
  exact (p.induce _ avoids).reachable

theorem crossing_edge (hG : G.IsTree) (C : Branch G r) {x y : V}
    (hx : x ∉ branchVerts C) (hy : y ∈ branchVerts C) (hxy : G.Adj x y) :
    x = r ∧ y = (attachment hG C).val.val := by
  obtain ⟨w,hw⟩ := hy
  change w.val.val = y at hw
  have he : x = r := by
    by_contra h
    let x' : Deleted r := ⟨x,h⟩
    have h' := same_branch_of_adj (G := G) (x := x') (y := w.val) (hw.symm ▸ hxy)
    exact hx ⟨⟨x',h'.trans w.property⟩,rfl⟩
  subst x
  have hh : w = attachment hG C :=
    (adj_iff_eq_attachment hG C w).mp (hw.symm ▸ hxy)
  exact ⟨rfl,hw.symm.trans (congrArg (fun w => w.val.val) hh)⟩

private theorem Walk.crosses {W : Type*} {H : SimpleGraph W} {u v : W}
    (w : H.Walk u v) (S : Set W) (hu : u ∉ S) (hv : v ∈ S) :
    ∃ x ∉ S, ∃ y ∈ S, H.Adj x y := by
  classical
  induction w with
  | nil => exact (hu hv).elim
  | @cons a b c hab p ih =>
    by_cases hb : b ∈ S
    · exact ⟨a,hu,b,hb,hab⟩
    · exact ih hb hv

def opposite (C : Branch G r) (z : C.supp) : Branch G z.val.val :=
  (cardAt G z.val.val).connectedComponentMk ⟨r,Ne.symm z.val.property⟩

theorem branch_compl_subset_opposite (hG : G.IsTree) (C : Branch G r) (z : C.supp) :
    (branchVerts C)ᶜ ⊆ branchVerts (opposite C z) := by
  intro x hx
  obtain ⟨hr,hx',h⟩ := outside_reachable_after_delete hG C z x hx
  exact ⟨⟨⟨x,hx'⟩,(ConnectedComponent.sound h).symm⟩,rfl⟩

theorem branch_compl_eq_adjacent_opposite (hG : G.IsTree) (C : Branch G r) :
    (branchVerts C)ᶜ = branchVerts (opposite C (attachment hG C)) := by
  apply (branch_compl_subset_opposite hG C _).antisymm
  intro x hx
  let z := attachment hG C
  rintro (hx' : x ∈ branchVerts C)
  obtain ⟨y,hy⟩ := hx
  have he : (cardAt G z.val.val).Reachable ⟨r,Ne.symm z.val.property⟩ y.val :=
    ConnectedComponent.exact y.property.symm
  obtain ⟨p⟩ := he
  let S : Set (Deleted z.val.val) := {v | v.val ∈ branchVerts C}
  have hstart : (⟨r,Ne.symm z.val.property⟩ : Deleted z.val.val) ∉ S :=
    root_not_branchVerts C
  have hend : y.val ∈ S := by
    change y.val.val ∈ branchVerts C
    change y.val.val = x at hy
    rwa [hy]
  obtain ⟨a,ha,b,hb,hab⟩ := Walk.crosses p S hstart hend
  exact b.property (crossing_edge hG C ha hb hab).2

theorem card_opposite_eq [Finite V] (hG : G.IsTree) (C : Branch G r) :
    Nat.card (opposite C (attachment hG C)).supp =
      Nat.card V - Nat.card C.supp := by
  rw [← card_branchVerts,← branch_compl_eq_adjacent_opposite hG C,
    Set.ncard_compl,card_branchVerts]

/-- The margin measures how far the largest branch is below half the tree. -/
def balanced {V : Type*} (G : SimpleGraph V) (r : V) (margin : ℕ) : Prop :=
  ∀ C : Branch G r, 2 * Nat.card C.supp + margin < Nat.card V

theorem balanced_unique [Finite V] (hG : G.IsTree) {z : V}
    (hr : balanced G r 0) (hz : balanced G z 0) : r = z := by
  by_contra h
  let z' : Deleted r := ⟨z,Ne.symm h⟩
  let C : Branch G r := (cardAt G r).connectedComponentMk z'
  let y : C.supp := ⟨z',rfl⟩
  have hc := Set.ncard_le_ncard (branch_compl_subset_opposite hG C y)
  rw [Set.ncard_compl,card_branchVerts,card_branchVerts] at hc
  have hl := hr C
  have hh := hz (opposite C y)
  omega

theorem balanced_congr {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {r : V} {s : W} (hr : Nat.card V = Nat.card W) (e : cardAt G r ≃g cardAt H s)
    {m : ℕ} (h : balanced G r m) : balanced H s m := by
  intro D
  obtain ⟨C,rfl⟩ := e.connectedComponentEquiv.surjective D
  rw [← Nat.card_congr (C.isoEquivSupp e),← hr]
  exact h C

theorem balanced_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {r : V} {m : ℕ} (h : balanced G r m) : balanced H (e r) m :=
  balanced_congr (Nat.card_congr e.toEquiv) (FiniteRootedTree.deletedIso e rfl) h

theorem balanced_leafCard (T : FiniteRootedTree.Tree) (l : T.V) (hn : T.r ≠ l)
    (hl : FiniteRootedTree.IsLeaf T l) (ht : balanced T.G T.r 1) :
    balanced (FiniteRootedTree.leafCard T l hn hl).G
      (FiniteRootedTree.leafCard T l hn hl).r 0 := by
  intro C
  let D := survivingBranch hn C
  have hsize := Nat.card_congr (branchOfLeafCardIso hn (FiniteRootedTree.unique_of_leaf hl) C).toEquiv
  have hle : Nat.card C.supp ≤ Nat.card D.supp :=
    hsize.trans_le (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)
  have hcard := FiniteRootedTree.order_leafCard T l hn hl
  change Nat.card (Deleted l) + 1 = Nat.card T.V at hcard
  have ht' := ht D
  change 2 * Nat.card C.supp + 0 < Nat.card (Deleted l)
  omega

theorem branch_count_of_balanced (T : FiniteRootedTree.Tree) (hV : 2 ≤ Nat.card T.V)
    (hbal : balanced T.G T.r 0) : 2 ≤ (FiniteRootedTree.branchMultiset T).card := by
  classical
  let _ : Fintype (Branch T.G T.r) := Fintype.ofFinite _
  have hc := card_eq_sum_branch_sizes T.G T.r
  have hsum : 0 < ∑ C : Branch T.G T.r, Nat.card C.supp := by omega
  obtain ⟨C,_,_⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hsum)
  by_contra! hsmall
  have hsmall' : Fintype.card (Branch T.G T.r) ≤ 1 := by
    have he : (FiniteRootedTree.branchMultiset T).card = Fintype.card (Branch T.G T.r) := by
      simp [FiniteRootedTree.branchMultiset]
    omega
  have hsub : Subsingleton (Branch T.G T.r) := by
    apply not_nontrivial_iff_subsingleton.mp
    intro hn
    have hh := Fintype.one_lt_card_iff_nontrivial.mpr hn
    omega
  have huniv : (Finset.univ : Finset (Branch T.G T.r)) = {C} := by
    ext z
    simp [Subsingleton.elim z C]
  rw [huniv,Finset.sum_singleton] at hc
  have hs := hbal C
  omega

/-- A centroid is a vertex with no branch containing more than half the vertices. -/
def isCentroid {V : Type*} (G : SimpleGraph V) (r : V) : Prop :=
  ∀ C : Branch G r, 2 * Nat.card C.supp ≤ Nat.card V

private noncomputable def maxBranchSize {V : Type*} [Finite V]
    (G : SimpleGraph V) (r : V) : ℕ :=
  let _ : Fintype (Branch G r) := Fintype.ofFinite _
  Finset.univ.sup (fun C : Branch G r => Nat.card C.supp)

private theorem size_le_max {V : Type*} [Finite V] (G : SimpleGraph V) (r : V)
    (C : Branch G r) : Nat.card C.supp ≤ maxBranchSize G r := by
  let _ : Fintype (Branch G r) := Fintype.ofFinite _
  exact Finset.le_sup (f := fun D : Branch G r => Nat.card D.supp) (Finset.mem_univ C)

private theorem sizes_le_max_of_bound {V : Type*} [Finite V] (G : SimpleGraph V) (r : V) (m : ℕ)
    (h : ∀ C : Branch G r, Nat.card C.supp ≤ m) : maxBranchSize G r ≤ m := by
  unfold maxBranchSize
  exact Finset.sup_le (fun C _ => h C)

private theorem other_branch_le [Finite V] {A B : Branch G r} (hne : A ≠ B) :
    Nat.card A.supp + Nat.card B.supp + 1 ≤ Nat.card V := by
  classical
  let _ : Fintype (Branch G r) := Fintype.ofFinite _
  have h := card_eq_sum_branch_sizes G r
  have hs : (∑ C ∈ ({A,B} : Finset (Branch G r)), Nat.card C.supp) ≤
      ∑ C : Branch G r, Nat.card C.supp :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_pair hne] at hs
  omega

theorem exists_centroid {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.IsTree) :
    ∃ r, isCentroid G r := by
  classical
  let _ := hG.nonempty
  let _ : Fintype V := Fintype.ofFinite _
  obtain ⟨r,_,hmin⟩ := Finset.exists_min_image Finset.univ (maxBranchSize G)
    (Finset.univ_nonempty (α := V))
  refine ⟨r,?_⟩
  unfold isCentroid
  by_contra! hc
  obtain ⟨C,hC⟩ := hc
  let z := (attachment hG C).val.val
  let D : Branch G z := opposite C (attachment hG C)
  have hD : Nat.card D.supp = Nat.card V - Nat.card C.supp := card_opposite_eq hG C
  have hdz : Nat.card C.supp ≤ Nat.card V :=
    Nat.card_le_card_of_injective (branchInclusion C) (branchInclusion C).injective
  have hall (E : Branch G z) : Nat.card E.supp ≤ Nat.card C.supp - 1 := by
    by_cases h : E = D
    · subst E
      omega
    · have hh := other_branch_le (Ne.symm h)
      omega
  have hlow := sizes_le_max_of_bound G z (Nat.card C.supp - 1) hall
  have hhigh := size_le_max G r C
  have hh := hmin z (Finset.mem_univ z)
  omega

theorem centroid_across_balanced_edge [Finite V] (hG : G.IsTree)
    (C : Branch G r) (he : 2 * Nat.card C.supp = Nat.card V) :
    isCentroid G (attachment hG C).val.val := by
  let z := (attachment hG C).val.val
  let D : Branch G z := opposite C (attachment hG C)
  have hD : Nat.card D.supp = Nat.card V - Nat.card C.supp := card_opposite_eq hG C
  intro E
  by_cases h : E = D
  · subst E
    omega
  · have hh := other_branch_le (Ne.symm h)
    omega

theorem second_centroid_adj [Finite V] (hG : G.IsTree) {z : V} (hn : r ≠ z)
    (hr : isCentroid G r) (hz : isCentroid G z) :
    G.Adj r z ∧ ∃ C : Branch G r, 2 * Nat.card C.supp = Nat.card V := by
  let z' : Deleted r := ⟨z,hn.symm⟩
  let C : Branch G r := (cardAt G r).connectedComponentMk z'
  let y : C.supp := ⟨z',rfl⟩
  let D := opposite C y
  have hsub := branch_compl_subset_opposite hG C y
  have hle := Set.ncard_le_ncard hsub
  rw [Set.ncard_compl,card_branchVerts,card_branchVerts] at hle
  change Nat.card V - Nat.card C.supp ≤ Nat.card D.supp at hle
  have hr' := hr C
  have hz' := hz D
  have heq : 2 * Nat.card C.supp = Nat.card V := by omega
  refine ⟨?_,C,heq⟩
  have hatt : (attachment hG C).val.val = z := by
    by_contra hne
    let a := (attachment hG C).val.val
    have ha : a ∈ branchVerts D := by
      let a' : Deleted z := ⟨a,hne⟩
      let r' : Deleted z := ⟨r,hn⟩
      have hAdj : (cardAt G z).Adj a' r' := (adj_attachment hG C).symm
      have hC := ConnectedComponent.sound hAdj.reachable
      exact ⟨⟨a',hC⟩,rfl⟩
    have hnot : a ∉ (branchVerts C)ᶜ := by
      intro h
      exact h ⟨attachment hG C,rfl⟩
    have hproper : (branchVerts C)ᶜ ⊂ branchVerts D := Set.ssubset_iff_subset_ne.mpr
      ⟨hsub,fun he => hnot (he.symm ▸ ha)⟩
    have hlt := Set.ncard_lt_ncard hproper
    rw [Set.ncard_compl,card_branchVerts,card_branchVerts] at hlt
    change Nat.card V - Nat.card C.supp < Nat.card D.supp at hlt
    omega
  exact hatt ▸ adj_attachment hG C

theorem balanced_of_even_unique_centroid [Finite V] (hG : G.IsTree)
    (hr : isCentroid G r) (hu : ∀ z, isCentroid G z → z = r)
    (hev : Even (Nat.card V)) : balanced G r 1 := by
  intro C
  have hc := hr C
  by_contra! hl
  obtain ⟨m,hm⟩ := hev
  have hhalf : 2 * Nat.card C.supp = Nat.card V := by omega
  have he := hu _ (centroid_across_balanced_edge hG C hhalf)
  exact (attachment hG C).val.property he

end

open FiniteRootedTree ReconstructionConjecture

/-- A sufficiently balanced centroid remains uniquely identifiable in every
leaf card, so the rooted reconstruction theorem applies. -/
theorem reconstruct_balanced {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (hV : 3 ≤ Fintype.card V) (hG : G.IsTree)
    (h : Hypomorphic G H) (r : V) (hr : balanced G r 1) : Nonempty (G ≃g H) := by
  classical
  have hH := TreeReconstruction.tree_of_hypomorphic hV hG h
  have hcardF := h.card_eq
  have hcard : Nat.card V = Nat.card W := by simpa only [Nat.card_eq_fintype_card] using hcardF
  have hsize : 2 ≤ Nat.card V := by rw [Nat.card_eq_fintype_card]; omega
  obtain ⟨σ,hσ,hdegree⟩ := TreeReconstruction.degree_preserving_hypomorphism hV h
  let T : Tree := ⟨V,G,r,hG,inferInstance⟩
  let U : Tree := ⟨W,H,σ r,hH,inferInstance⟩
  have hs : balanced H (σ r) 1 := balanced_congr hcard (hσ r).some hr
  have weak {A : Type} {K : SimpleGraph A} {o : A} (hk : balanced K o 1) : balanced K o 0 := by
    intro C
    have hc := hk C
    omega
  have hbranchesT : 2 ≤ (branchMultiset T).card := branch_count_of_balanced T hsize (weak hr)
  have hbranchesU : 2 ≤ (branchMultiset U).card := branch_count_of_balanced U (hcard ▸ hsize) (weak hs)
  have hleaf (x : V) : IsLeaf T x ↔ IsLeaf U (σ x) :=
    (leaf_iff_card_neighbor T x).trans
      ((congrArg (· = 1) (hdegree x)).to_iff.trans (leaf_iff_card_neighbor U (σ x)).symm)
  have cards (x : V) (hx : r ≠ x) (hl : IsLeaf T x) :
      Related (leafCard T x hx hl)
        (leafCard U (σ x) (σ.injective.ne hx) ((hleaf x).mp hl)) := by
    let e := (hσ x).some
    refine ⟨e,?_⟩
    exact balanced_unique (leafCard U (σ x) (σ.injective.ne hx) ((hleaf x).mp hl)).connected
      (balanced_iso e (balanced_leafCard T x hx hl hr))
      (balanced_leafCard U (σ x) (σ.injective.ne hx) ((hleaf x).mp hl) hs)
  have he : rootedCards T = rootedCards U := by
    ext K
    constructor
    · rintro ⟨x,hx,hl,rfl⟩
      exact ⟨σ x,σ.injective.ne hx,(hleaf x).mp hl,(ofTree_eq_iff.mpr (cards x hx hl)).symm⟩
    · rintro ⟨y,hy,hl,rfl⟩
      obtain ⟨x,rfl⟩ := σ.surjective y
      have hx : r ≠ x := fun hh => hy (congrArg σ hh)
      have hl' := (hleaf x).mpr hl
      exact ⟨x,hx,hl',ofTree_eq_iff.mpr (cards x hx hl')⟩
  obtain ⟨e,_⟩ := related_of_rootedCards_eq hbranchesT hbranchesU he
  exact ⟨e⟩

theorem reconstruct_even_unique_centroid {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (hV : 3 ≤ Fintype.card V) (hG : G.IsTree)
    (h : Hypomorphic G H) (he : Even (Nat.card V)) (hc : ∃! r, isCentroid G r) :
    Nonempty (G ≃g H) := by
  obtain ⟨r,hr,hu⟩ := hc
  exact reconstruct_balanced hV hG h r (balanced_of_even_unique_centroid hG hr hu he)

end TreeCentroid

/- Unordered pairs of rooted branches in balanced cards. -/

namespace CentroidPairDeck

/-- Each card has one fixed branch and one branch from the given trim set. -/
def oneSide {α : Type*} (a : α) (trim : Set α) : Set (Multiset α) :=
  (fun x => ({a,x} : Multiset α)) '' trim

theorem oneSide_injective {α : Type*} {a b : α} {trim : Set α}
    (ht : trim.Nonempty) (h : oneSide a trim = oneSide b trim) : a = b := by
  classical
  by_contra hne
  have aux {x y : α} (hn : x ≠ y) (hh : oneSide x trim = oneSide y trim)
      (z : α) (hz : z ∈ trim) : z = y := by
    have hc : ({x,z} : Multiset α) ∈ oneSide y trim := hh ▸ ⟨z,hz,rfl⟩
    obtain ⟨t,ht,hpair⟩ := hc
    have hy : y ∈ ({x,z} : Multiset α) := hpair ▸ by simp
    exact (by simpa [hn.symm] using hy : y = z).symm
  obtain ⟨z,hz⟩ := ht
  exact hne ((aux hne h z hz).symm.trans (aux (Ne.symm hne) h.symm z hz)).symm

/-- A deck of balanced cards records both possible sides as unordered
pairs. Each move trims one side and preserves the other. -/
def twoSides {α : Type*} (trim : α → Set α) (a b : α) : Set (Multiset α) :=
  oneSide a (trim b) ∪ oneSide b (trim a)

theorem retain_those_without {α : Type*} {trim : α → Set α} {a b : α}
    (ha : a ∉ trim a) (hb : b ≠ a) :
    {m ∈ twoSides trim a b | a ∉ m} = oneSide b (trim a) := by
  classical
  ext m
  constructor
  · intro h
    rcases h.1 with h'|h'
    · obtain ⟨x,hx,rfl⟩ := h'
      exact (h.2 (by simp)).elim
    · exact h'
  · rintro ⟨x,hx,rfl⟩
    refine ⟨Or.inr ⟨x,hx,rfl⟩,?_⟩
    simp [hb.symm,(ne_of_mem_of_not_mem hx ha).symm]

theorem twoSides_eq_fixed_branch {α : Type*} {trim : α → Set α} {a b c : α}
    (ha : a ∉ trim a) (ht : (trim a).Nonempty)
    (h : twoSides trim a b = twoSides trim a c) : b = c := by
  classical
  by_cases hb : b = a
  · subst b
    by_contra hc
    obtain ⟨x,hx⟩ := ht
    have hcx : ({c,x} : Multiset α) ∈ {m ∈ twoSides trim a c | a ∉ m} :=
      (retain_those_without ha (Ne.symm hc)).symm ▸ ⟨x,hx,rfl⟩
    rw [← h] at hcx
    rcases hcx.1 with h'|h' <;>
      obtain ⟨z,_,hz⟩ := h' <;>
      exact (hcx.2 (hz ▸ by simp)).elim
  by_cases hc : c = a
  · subst c
    obtain ⟨x,hx⟩ := ht
    have hbx : ({b,x} : Multiset α) ∈ {m ∈ twoSides trim a b | a ∉ m} :=
      (retain_those_without ha hb).symm ▸ ⟨x,hx,rfl⟩
    rw [h] at hbx
    rcases hbx.1 with h'|h' <;>
      obtain ⟨z,_,hz⟩ := h' <;>
      exact (hbx.2 (hz ▸ by simp)).elim
  apply oneSide_injective ht
  rw [← retain_those_without ha hb,← retain_those_without ha hc,h]

end CentroidPairDeck

namespace TreeHalf

open SimpleGraph TreeCentroid TreeBranches FiniteRootedTree

section Cut

variable {V : Type} {G : SimpleGraph V} {r z : V}

def toward (h : G.Adj r z) : Branch G r :=
  (cardAt G r).connectedComponentMk ⟨z,h.ne'⟩

def cut (h : G.Adj r z) : Set V := branchVerts (toward h)

def inside (h : G.Adj r z) : cut h := ⟨z,⟨⟨⟨z,h.ne'⟩,rfl⟩,rfl⟩⟩

def outside (h : G.Adj r z) : ((cut h)ᶜ : Set V) := ⟨r,root_not_branchVerts (toward h)⟩

theorem attachment_toward (hG : G.IsTree) (h : G.Adj r z) :
    attachment hG (toward h) = ⟨⟨z,h.ne'⟩,rfl⟩ :=
  ((adj_iff_eq_attachment hG (toward h) ⟨⟨z,h.ne'⟩,rfl⟩).mp h).symm

theorem cut_symm (hG : G.IsTree) (h : G.Adj r z) : cut h.symm = (cut h)ᶜ := by
  have hc := branch_compl_eq_adjacent_opposite hG (toward h)
  rw [attachment_toward hG h] at hc
  exact hc.symm

private noncomputable def cutIso (h : G.Adj r z) :
    BranchGraph (toward h) ≃g G.induce (cut h) := by
  let e : (toward h).supp ≃ cut h :=
    Equiv.ofBijective (fun x => ⟨x.val.val,⟨x,rfl⟩⟩)
      ⟨fun x y hh => Subtype.ext (Subtype.ext (congrArg (fun q : cut h => q.val) hh)),
        fun ⟨_,x,hx⟩ => ⟨x,Subtype.ext hx⟩⟩
  exact ⟨e,Iff.rfl⟩

noncomputable abbrev half [Finite V] (hG : G.IsTree) (h : G.Adj r z) : Tree :=
  ⟨cut h,G.induce (cut h),inside h,(cutIso h).isTree_iff.mp (branch_isTree hG _),inferInstance⟩

noncomputable def halfClass [Finite V] (hG : G.IsTree) (h : G.Adj r z) : FiniteRootedTree.Class :=
  ofTree (half hG h)

theorem halfClass_eq_branch [Finite V] (hG : G.IsTree) (h : G.Adj r z) :
    halfClass hG h = branchClass (⟨V,G,r,hG,inferInstance⟩ : Tree) (toward h) := by
  apply ofTree_eq_iff.mpr
  refine ⟨(cutIso h).symm,?_⟩
  apply ((cutIso h).symm_apply_eq).mpr
  exact Subtype.ext (congrArg (fun x => x.val.val) (attachment_toward hG h).symm)

theorem opposite_half_order [Finite V] (hG : G.IsTree) (h : G.Adj r z) :
    order (halfClass hG h.symm) = Nat.card V - order (halfClass hG h) := by
  change Nat.card (cut h.symm) = Nat.card V - Nat.card (cut h)
  rw [cut_symm hG h,Nat.card_coe_set_eq,Nat.card_coe_set_eq,Set.ncard_compl]

theorem leaf_half_iff [Finite V] (hG : G.IsTree) (h : G.Adj r z) (x : cut h)
    (hx : x.val ≠ z) :
    IsLeaf (half hG h) x ↔ ∃! y, G.Adj x.val y := by
  let e := cutIso h
  let y := e.symm x
  have hxy : y.val.val = x.val := congrArg Subtype.val (e.apply_symm_apply x)
  let T : Tree := ⟨V,G,r,hG,inferInstance⟩
  have hy : y ≠ attachment hG (toward h) := by
    intro hh
    apply hx
    rw [← hxy,hh,attachment_toward hG h]
  rw [leaf_iff_card_neighbor]
  change Nat.card ((G.induce (cut h)).neighborSet x) = 1 ↔ _
  have he : e y = x := e.apply_symm_apply x
  rw [← he]
  have h1 := Nat.card_congr (e.mapNeighborSet y)
  rw [← h1]
  have h2 := leaf_in_branch_iff T (toward h) y hy
  rw [leaf_iff_card_neighbor] at h2
  rw [h2]
  change (∃! w, G.Adj y.val.val w) ↔ ∃! w, G.Adj (e y).val w
  rw [he,hxy]

theorem edge_end_not_leaf [Finite V] (hG : G.IsTree) (h : G.Adj r z)
    (hlarge : 2 ≤ order (halfClass hG h)) : ¬ (∃! y, G.Adj z y) := by
  intro hl
  let T : Tree := ⟨V,G,r,hG,inferInstance⟩
  have hLeaf : IsLeaf T (attachment hG (toward h)).val.val := by
    change ∃! x, G.Adj (attachment hG (toward h)).val.val x
    rwa [attachment_toward hG h]
  have hx := singleton_branch_of_leaf_root T (toward h) hLeaf
  rw [halfClass_eq_branch hG h] at hlarge
  change 2 ≤ order (branchClass T (toward h)) at hlarge
  omega

end Cut

/-- Reattaching two rooted halves by their root edge. -/
theorem assemble {V W : Type} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} {r z : V} {s w : W}
    (hG : G.IsTree) (hH : H.IsTree) (h : G.Adj r z) (h' : H.Adj s w)
    (h₁ : halfClass hG h = halfClass hH h') (h₂ : halfClass hG h.symm = halfClass hH h'.symm) :
    Nonempty (G ≃g H) := by
  classical
  obtain ⟨f,hf⟩ := ofTree_eq_iff.mp h₁
  obtain ⟨g,hg⟩ := ofTree_eq_iff.mp h₂
  let isoV : cut h.symm ≃ ((cut h)ᶜ : Set V) := Equiv.setCongr (cut_symm hG h)
  let isoW : cut h'.symm ≃ ((cut h')ᶜ : Set W) := Equiv.setCongr (cut_symm hH h')
  let e₀ := isoV.symm.trans (g.toEquiv.trans isoW)
  let e := (Equiv.Set.sumCompl (cut h)).symm.trans
    ((Equiv.sumCongr f.toEquiv e₀).trans (Equiv.Set.sumCompl (cut h')))
  have hIn (x : cut h) : e x.val = (f x).val := by
    simp [e,Equiv.Set.sumCompl_symm_apply_of_mem x.property]
  have hOut (x : ((cut h)ᶜ : Set V)) : e x.val = (g (isoV.symm x)).val := by
    simp [e,e₀,isoW,Equiv.Set.sumCompl_symm_apply_of_notMem x.property]
  have er : e r = s := by
    rw [show r = (outside h).val from rfl,hOut]
    exact congrArg Subtype.val hg
  have ez : e z = w := by
    rw [show z = (inside h).val from rfl,hIn]
    exact congrArg Subtype.val hf
  have hmem (x : V) : e x ∈ cut h' ↔ x ∈ cut h := by
    by_cases hx : x ∈ cut h
    · exact iff_of_true (by rw [hIn ⟨x,hx⟩]; exact (f ⟨x,hx⟩).property) hx
    · exact iff_of_false (by rw [hOut ⟨x,hx⟩]; exact (isoW (g (isoV.symm ⟨x,hx⟩))).property) hx
  have cross (x y : V) (hx : x ∉ cut h) (hy : y ∈ cut h) :
      H.Adj (e x) (e y) ↔ G.Adj x y := by
    have hSideG (hadj : G.Adj x y) : x = r ∧ y = z := by
      have hcross := crossing_edge hG (toward h) hx hy hadj
      rw [attachment_toward hG h] at hcross
      exact hcross
    have hSideH (hadj : H.Adj (e x) (e y)) : e x = s ∧ e y = w := by
      have hcross := crossing_edge hH (toward h') ((hmem x).not.mpr hx) ((hmem y).mpr hy) hadj
      rw [attachment_toward hH h'] at hcross
      exact hcross
    constructor
    · intro hadj
      obtain ⟨h₁,h₂⟩ := hSideH hadj
      rw [← er] at h₁
      rw [← ez] at h₂
      rw [e.injective h₁,e.injective h₂]
      exact h
    · intro hadj
      obtain ⟨h₁,h₂⟩ := hSideG hadj
      rwa [h₁,h₂,er,ez]
  refine ⟨⟨e,?_⟩⟩
  intro x y
  by_cases hx : x ∈ cut h <;> by_cases hy : y ∈ cut h
  · rw [hIn ⟨x,hx⟩,hIn ⟨y,hy⟩]
    exact f.map_rel_iff
  · rw [adj_comm H,adj_comm G]
    exact cross y x hy hx
  · exact cross x y hx hy
  · rw [hOut ⟨x,hx⟩,hOut ⟨y,hy⟩]
    exact g.map_rel_iff

section Leaf

variable {V : Type} {G : SimpleGraph V} {r z l : V}

private theorem mem_cut_iff (h : G.Adj r z) (x : V) :
    x ∈ cut h ↔ ∃ hx : x ≠ r, (cardAt G r).Reachable ⟨z,h.ne'⟩ ⟨x,hx⟩ := by
  constructor
  · rintro ⟨u,hu⟩
    have he : u.val.val = x := hu
    have hh : (cardAt G r).Reachable ⟨z,h.ne'⟩ u.val :=
      ConnectedComponent.exact u.property.symm
    have hx : x ≠ r := he ▸ u.val.property
    exact ⟨hx,by
      have hp : u.val = (⟨x,hx⟩ : Deleted r) := Subtype.ext he
      rwa [← hp]⟩
  · rintro ⟨hx,hreach⟩
    exact ⟨⟨⟨x,hx⟩,(ConnectedComponent.sound hreach).symm⟩,rfl⟩

theorem edgeOnCard (h : G.Adj r z) (hr : r ≠ l) (hz : z ≠ l) :
    (cardAt G l).Adj (newRoot hr) (newRoot hz) := h

theorem card_cut (h : G.Adj r z) (hr : r ≠ l) (hz : z ≠ l)
    (hl : ∀ a b, G.Adj l a → G.Adj l b → a = b) (x : Deleted l) :
    x ∈ cut (edgeOnCard h hr hz) ↔ x.val ∈ cut h := by
  rw [mem_cut_iff,mem_cut_iff]
  constructor
  · rintro ⟨hx,hreach⟩
    have hx' : x.val ≠ r := fun hh => hx (Subtype.ext hh)
    refine ⟨hx',?_⟩
    let x₀ : Deleted r := ⟨x.val,hx'⟩
    let x₁ : Deleted (removedInBranch hr) := ⟨x₀,fun hh => x.property (congrArg Subtype.val hh)⟩
    let z₁ : Deleted (removedInBranch hr) := ⟨⟨z,h.ne'⟩,fun hh => hz (congrArg Subtype.val hh)⟩
    have hr' : (cardAt (cardAt G r) (removedInBranch hr)).Reachable z₁ x₁ :=
      hreach.map (switchCards (G := G) hr).toHom
    exact (reachable_card_iff (removedInBranch hr) (leaf_unique_in_card hr hl) z₁ x₁).mp hr'
  · rintro ⟨hx,hreach⟩
    have hx' : x ≠ newRoot hr := fun hh => hx (congrArg Subtype.val hh)
    refine ⟨hx',?_⟩
    let x₀ : Deleted r := ⟨x.val,hx⟩
    let x₁ : Deleted (removedInBranch hr) := ⟨x₀,fun hh => x.property (congrArg Subtype.val hh)⟩
    let z₁ : Deleted (removedInBranch hr) := ⟨⟨z,h.ne'⟩,fun hh => hz (congrArg Subtype.val hh)⟩
    have hr' := (reachable_card_iff (removedInBranch hr) (leaf_unique_in_card hr hl) z₁ x₁).mpr hreach
    exact hr'.map (switchCards (G := G) hr).symm.toHom

/-- A leaf card preserves the opposite half and trims the half containing the leaf. -/
def inducedHalfIso (h : G.Adj r z) (hr : r ≠ l) (hz : z ≠ l)
    (hl : ∀ a b, G.Adj l a → G.Adj l b → a = b) :
    (cardAt G l).induce (cut (edgeOnCard h hr hz)) ≃g
      (G.induce (cut h)).induce {x | x.val ≠ l} where
  toEquiv := {
    toFun := fun x => ⟨⟨x.val.val,(card_cut h hr hz hl x.val).mp x.property⟩,x.val.property⟩
    invFun := fun x => ⟨⟨x.val.val,x.property⟩,(card_cut h hr hz hl ⟨x.val.val,x.property⟩).mpr x.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

variable [Finite V]

private abbrev rootAt (G : SimpleGraph V) (hG : G.IsTree) (r : V) : Tree :=
  ⟨V,G,r,hG,inferInstance⟩

private theorem leafHalfIn (hG : G.IsTree) (h : G.Adj r z) (hz : z ≠ l)
    (hl : IsLeaf (rootAt G hG r) l) (hin : l ∈ cut h) :
    IsLeaf (half hG h) ⟨l,hin⟩ :=
  (leaf_half_iff hG h ⟨l,hin⟩ hz.symm).mpr hl

theorem halfClass_leaf_in (hG : G.IsTree) (h : G.Adj r z) (hr : r ≠ l) (hz : z ≠ l)
    (hl : IsLeaf (rootAt G hG r) l) (hin : l ∈ cut h) :
    halfClass (leafCard (rootAt G hG r) l hr hl).connected (edgeOnCard h hr hz) =
      ofTree (leafCard (half hG h) ⟨l,hin⟩ (fun he => hz (congrArg Subtype.val he))
        (leafHalfIn hG h hz hl hin)) := by
  have hs : ({x | x.val ≠ l} : Set (cut h)) = {⟨l,hin⟩}ᶜ := by
    ext x
    change x.val ≠ l ↔ x ≠ (⟨l,hin⟩ : cut h)
    exact not_congr ⟨fun he => Subtype.ext he,fun he => congrArg (fun x : cut h => x.val) he⟩
  apply ofTree_eq_iff.mpr
  exact ⟨(inducedHalfIso h hr hz (unique_of_leaf hl)).trans (FiniteRootedTree.setInduceIso _ hs),rfl⟩

theorem halfClass_leaf_out (hG : G.IsTree) (h : G.Adj r z) (hr : r ≠ l) (hz : z ≠ l)
    (hl : IsLeaf (rootAt G hG r) l) (hout : l ∉ cut h) :
    halfClass (leafCard (rootAt G hG r) l hr hl).connected (edgeOnCard h hr hz) =
      halfClass hG h := by
  have hs : ({x | x.val ≠ l} : Set (cut h)) = Set.univ := by
    ext x
    change x.val ≠ l ↔ x ∈ (Set.univ : Set (cut h))
    exact iff_of_true (fun he => hout (he ▸ x.property)) (Set.mem_univ x)
  apply ofTree_eq_iff.mpr
  exact ⟨(inducedHalfIso h hr hz (unique_of_leaf hl)).trans
    ((FiniteRootedTree.setInduceIso _ hs).trans (SimpleGraph.induceUnivIso _)),rfl⟩

end Leaf

section RemovingComponent

variable {V : Type*} {G : SimpleGraph V} (C : G.ConnectedComponent)

abbrev OffComponent := (C.supp)ᶜ

def remainingComponents (X : (G.induce (OffComponent C)).ConnectedComponent) :
    G.ConnectedComponent :=
  X.map (SimpleGraph.Embedding.induce _).toHom

private theorem remainingComponents_apply (x : OffComponent C) :
    remainingComponents C ((G.induce (OffComponent C)).connectedComponentMk x) =
      G.connectedComponentMk x.val := rfl

theorem reachable_off_component (x y : OffComponent C) :
    (G.induce (OffComponent C)).Reachable x y ↔ G.Reachable x.val y.val := by
  constructor
  · exact fun h => h.map (SimpleGraph.Embedding.induce _).toHom
  · rintro ⟨w⟩
    have hm (u : V) (hu : u ∈ w.support) : u ∈ OffComponent C := by
      obtain ⟨p,_,_⟩ := w.mem_support_iff_exists_append.mp hu
      exact fun hh => x.property ((ConnectedComponent.sound p.reachable).trans hh)
    exact (w.induce _ hm).reachable

theorem remainingComponents_injective : Function.Injective (remainingComponents C) := by
  intro D E
  refine ConnectedComponent.ind₂ ?_ D E
  intro x y he
  rw [remainingComponents_apply,remainingComponents_apply,ConnectedComponent.eq] at he
  exact ConnectedComponent.sound ((reachable_off_component C x y).mpr he)

noncomputable def offComponentEquiv :
    (G.induce (OffComponent C)).ConnectedComponent ≃ {D : G.ConnectedComponent // D ≠ C} := by
  let f (D : (G.induce (OffComponent C)).ConnectedComponent) :
      {D : G.ConnectedComponent // D ≠ C} :=
    ⟨remainingComponents C D,by
      refine D.ind ?_
      exact fun x => x.property⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro D E h
    exact remainingComponents_injective C (congrArg Subtype.val h)
  · rintro ⟨D,hd⟩
    obtain ⟨x,hx⟩ := D.nonempty_supp
    let x' : OffComponent C := ⟨x,fun hh => hd (hx.symm.trans hh)⟩
    exact ⟨(G.induce (OffComponent C)).connectedComponentMk x',Subtype.ext hx⟩

def offComponentIso (D : (G.induce (OffComponent C)).ConnectedComponent) :
    D.toSimpleGraph ≃g (remainingComponents C D).toSimpleGraph := by
  have hne (x : (remainingComponents C D).supp) : x.val ∉ C.supp := by
    intro hx
    exact ((offComponentEquiv C D).property) (x.property.symm.trans hx)
  refine {toEquiv := {
    toFun := fun x => ⟨x.val.val,?_⟩
    invFun := fun x => ⟨⟨x.val,hne x⟩,?_⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl },map_rel_iff' := Iff.rfl }
  · exact congrArg (remainingComponents C) x.property
  · apply remainingComponents_injective C
    rw [remainingComponents_apply]
    exact x.property

end RemovingComponent

section BranchList

variable {V : Type} [Finite V] {G : SimpleGraph V} {r z : V}

private def branchesAwayGraphIso (hG : G.IsTree) (h : G.Adj r z) :
    cardAt (half hG h.symm).G (half hG h.symm).r ≃g
      (cardAt G r).induce (OffComponent (toward h)) := by
  have hm (x : cut h.symm) (hx : x ≠ inside h.symm) :
      (⟨x.val,fun hh => hx (Subtype.ext hh)⟩ : Deleted r) ∈ OffComponent (toward h) := by
    intro hh
    have hc : x.val ∈ (cut h)ᶜ := cut_symm hG h ▸ x.property
    exact hc ⟨⟨_,hh⟩,rfl⟩
  have hn (x : OffComponent (toward h)) : x.val.val ∈ cut h.symm := by
    rw [cut_symm hG h]
    rintro ⟨y,hy⟩
    exact x.property ((show y.val = x.val from Subtype.ext hy) ▸ y.property)
  refine {toEquiv := {
    toFun := fun x => ⟨⟨x.val.val,fun hh => x.property (Subtype.ext hh)⟩,hm x.val x.property⟩
    invFun := fun x => ⟨⟨x.val.val,hn x⟩,fun hh => x.val.property (congrArg Subtype.val hh)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl },map_rel_iff' := Iff.rfl }

private noncomputable def branchesAwayEquiv (hG : G.IsTree) (h : G.Adj r z) :
    Branch (half hG h.symm).G (half hG h.symm).r ≃ {C : Branch G r // C ≠ toward h} :=
  (branchesAwayGraphIso hG h).connectedComponentEquiv.trans (offComponentEquiv (toward h))

private theorem branchAway_class (hG : G.IsTree) (h : G.Adj r z)
    (C : Branch (half hG h.symm).G (half hG h.symm).r) :
    branchClass (half hG h.symm) C =
      branchClass (rootAt G hG r) (branchesAwayEquiv hG h C).val := by
  let e := branchesAwayGraphIso hG h
  let f := (restrictComponentIso e C).trans
    (offComponentIso (toward h) (e.connectedComponentEquiv C))
  apply ofTree_eq_iff.mpr
  refine ⟨f,?_⟩
  apply (adj_iff_eq_attachment hG _ _).mp
  exact adj_attachment (half hG h.symm).connected C

/-- The branch list at an endpoint consists of its neighbor's whole half
and the branches of the endpoint's own half. -/
theorem branchMultiset_split_half (hG : G.IsTree) (h : G.Adj r z) :
    branchMultiset (rootAt G hG r) =
      halfClass hG h ::ₘ branchMultiset (half hG h.symm) := by
  rw [halfClass_eq_branch hG h]
  have hs := FiniteRootedTree.enum_split (branchClass (rootAt G hG r)) (toward h)
  have hi := FiniteRootedTree.enum_congr (branchesAwayEquiv hG h)
    (branchClass (half hG h.symm))
    (fun x => branchClass (rootAt G hG r) x.val)
    (branchAway_class hG h)
  exact hs.trans (congrArg (branchClass (rootAt G hG r) (toward h) ::ₘ ·) hi.symm)

end BranchList

end TreeHalf

namespace RootedClass

open FiniteRootedTree TreeBranches

noncomputable def children : FiniteRootedTree.Class → Multiset FiniteRootedTree.Class :=
  Quotient.lift branchMultiset (fun _ _ h => branchMultiset_related h)

theorem children_ofTree (T : Tree) : children (ofTree T) = branchMultiset T := rfl

theorem children_injective : Function.Injective children := by
  intro a b
  refine Quotient.inductionOn₂ a b (fun T U h => ?_)
  exact ofTree_eq_iff.mpr (related_of_branchMultiset h)

theorem order_eq_children_sum (a : FiniteRootedTree.Class) :
    order a = 1 + ((children a).map order).sum := by
  refine Quotient.inductionOn a (fun T => ?_)
  classical
  let _ : Fintype (Branch T.G T.r) := Fintype.ofFinite _
  have h := card_eq_sum_branch_sizes T.G T.r
  change Nat.card T.V = 1 + ((branchMultiset T).map order).sum
  rw [branchMultiset,Multiset.map_map]
  exact h

theorem child_order_lt {a b : FiniteRootedTree.Class} (hb : b ∈ children a) :
    order b < order a := by
  rw [order_eq_children_sum a]
  have hb' := Multiset.mem_map_of_mem order hb
  have hh := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) (order b) hb'
  omega

theorem child_order_add_two_le {a b : FiniteRootedTree.Class} (hb : b ∈ children a)
    (ha : 2 ≤ (children a).card) : order b + 2 ≤ order a := by
  obtain ⟨r,hr⟩ := Multiset.exists_cons_of_mem hb
  have hpos : 0 < r.card := by rw [hr,Multiset.card_cons] at ha; omega
  obtain ⟨x,hx⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  have hx' := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) (order x) (Multiset.mem_map_of_mem order hx)
  have hp := order_pos x
  rw [order_eq_children_sum a,hr,Multiset.map_cons,Multiset.sum_cons]
  omega

def trims (t : FiniteRootedTree.Class) : Set FiniteRootedTree.Class := {u | trim t (some u)}

theorem trim_order {a b : FiniteRootedTree.Class} (h : b ∈ trims a) :
    order b + 1 = order a := trim_size a (some b) h

theorem trims_nonempty {a : FiniteRootedTree.Class} (ha : 2 ≤ order a) : (trims a).Nonempty := by
  obtain ⟨t,ht⟩ := trim_exists a
  cases t with
  | none =>
    have h := trim_size _ _ ht
    simp at h
    omega
  | some t => exact ⟨t,ht⟩

theorem children_nonempty {a : FiniteRootedTree.Class} (ha : 2 ≤ order a) :
    0 < (children a).card := by
  by_contra! hw
  have hz : children a = 0 := Multiset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hw)
  rw [order_eq_children_sum a,hz,Multiset.map_zero,Multiset.sum_zero] at ha
  omega

theorem trim_children {a b : FiniteRootedTree.Class} (h : b ∈ trims a) :
    children b ∈ RootedBranchDeck.cards trim (children a) := by
  refine Quotient.inductionOn₂ a b (fun T U h => ?_) h
  obtain ⟨l,hn,hl,he⟩ := (trim_some_ofTree_iff T (ofTree U)).mp h
  change branchMultiset U ∈ RootedBranchDeck.cards trim (branchMultiset T)
  rw [cards_branchMultiset]
  exact ⟨l,hn,hl,branchMultiset_related (ofTree_eq_iff.mp he)⟩

end RootedClass

namespace EvenCentroidProfile

open FiniteRootedTree RootedClass Multiset

abbrev Shape := FiniteRootedTree.Class

def one (a b : Shape) : Set (Multiset Shape) := (fun x => x ::ₘ children a) '' trims b

def cards (a b : Shape) : Set (Multiset Shape) := one a b ∪ one b a

theorem cards_comm (a b : Shape) : cards a b = cards b a := Set.union_comm _ _

private theorem recover_larger {a b x y : Shape} (hab : order a = order b)
    (hx : order x + 1 = order a) (hy : order y + 1 = order b)
    (ha : 2 ≤ (children a).card) (h : x ::ₘ children a = y ::ₘ children b) :
    a = b := by
  have hm : y ∈ x ::ₘ children a := by rw [h]; simp
  have he := (Multiset.mem_cons.mp hm).resolve_right (fun hh => by
    have hle := child_order_add_two_le hh ha
    omega)
  subst y
  exact children_injective ((Multiset.cons_inj_right _).mp h)

private theorem matches_nonunary {a b c d : Shape}
    (hab : order a = order b) (hac : order a = order c) (had : order a = order d)
    (ha : 2 ≤ order a) (han : 2 ≤ (children a).card) (h : cards a b = cards c d) :
    a = c ∨ a = d := by
  obtain ⟨x,hx⟩ := trims_nonempty (hab ▸ ha)
  have hm : x ::ₘ children a ∈ cards c d := h ▸ Or.inl ⟨x,hx,rfl⟩
  have hxo := trim_order hx
  rcases hm with hleft|hright
  · obtain ⟨y,hy,he⟩ := hleft
    have hyo : order y + 1 = order c := (trim_order hy).trans (had.symm.trans hac)
    exact Or.inl (recover_larger hac (hxo.trans hab.symm) hyo han he.symm)
  · obtain ⟨y,hy,he⟩ := hright
    have hyo : order y + 1 = order d := (trim_order hy).trans (hac.symm.trans had)
    exact Or.inr (recover_larger had (hxo.trans hab.symm) hyo han he.symm)

private theorem has_card_two {a b : Shape} (ha : 2 ≤ order a) (hb : 2 ≤ order b) :
    (∃ m ∈ cards a b, m.card = 2) ↔ (children a).card = 1 ∨ (children b).card = 1 := by
  constructor
  · rintro ⟨m,hm,hc⟩
    rcases hm with hleft|hright
    · obtain ⟨x,hx,rfl⟩ := hleft
      simp only [Multiset.card_cons] at hc
      exact Or.inl (by omega)
    · obtain ⟨x,hx,rfl⟩ := hright
      simp only [Multiset.card_cons] at hc
      exact Or.inr (by omega)
  · intro h
    rcases h with hl|hr
    · obtain ⟨y,hy⟩ := trims_nonempty hb
      exact ⟨y ::ₘ children a,Or.inl ⟨y,hy,rfl⟩,by simp [hl]⟩
    · obtain ⟨y,hy⟩ := trims_nonempty ha
      exact ⟨y ::ₘ children b,Or.inr ⟨y,hy,rfl⟩,by simp [hr]⟩

private theorem two_card_set {a b x : Shape}
    (h : 2 ≤ (children a).card) (hx : children b = {x}) :
    {m ∈ cards a b | m.card = 2} = CentroidPairDeck.oneSide x (trims a) := by
  ext m
  constructor
  · rintro ⟨hm,hc⟩
    rcases hm with hm|hm
    · obtain ⟨z,_,rfl⟩ := hm
      simp only [Multiset.card_cons] at hc
      omega
    · obtain ⟨z,hz,rfl⟩ := hm
      exact ⟨z,hz,by rw [hx]; exact Multiset.cons_swap _ _ _⟩
  · rintro ⟨z,hz,rfl⟩
    refine ⟨Or.inr ⟨z,hz,?_⟩,by simp⟩
    rw [hx]
    exact Multiset.cons_swap _ _ _

private theorem recover_with_fixed_nonunary {a b d : Shape}
    (hab : order a = order b) (had : order a = order d)
    (ha : 2 ≤ order a) (han : 2 ≤ (children a).card) (h : cards a b = cards a d) : b = d := by
  have hb : 2 ≤ order b := hab ▸ ha
  have hd : 2 ≤ order d := had ▸ ha
  have hm : (children b).card = 1 ↔ (children d).card = 1 := by
    have hbl := has_card_two ha hb
    have hdl := has_card_two ha hd
    rw [h] at hbl
    have hn : (children a).card ≠ 1 := by omega
    simpa [hn] using hbl.symm.trans hdl
  by_cases hbu : (children b).card = 1
  · have hdu := hm.mp hbu
    obtain ⟨x,hx⟩ := Multiset.card_eq_one.mp hbu
    obtain ⟨y,hy⟩ := Multiset.card_eq_one.mp hdu
    have hset : CentroidPairDeck.oneSide x (trims a) = CentroidPairDeck.oneSide y (trims a) := by
      rw [← two_card_set han hx,← two_card_set han hy,h]
    have hxy := CentroidPairDeck.oneSide_injective (trims_nonempty ha) hset
    exact children_injective (hx.trans (by simpa [hxy] using hy.symm))
  · have hb2 : 2 ≤ (children b).card := by have hp := children_nonempty hb; omega
    have hd2 : 2 ≤ (children d).card := by
      have hp := children_nonempty hd
      have hn := (not_congr hm).mp hbu
      omega
    have hbmatch : b = a ∨ b = d :=
      matches_nonunary hab.symm hab.symm (hab.symm.trans had) hb hb2
        ((cards_comm b a).trans h)
    rcases hbmatch with hba|hbd
    · subst b
      have hdmatch : d = a ∨ d = a :=
        matches_nonunary had.symm had.symm had.symm hd hd2 ((cards_comm d a).trans h.symm)
      exact (hdmatch.elim id id).symm
    · exact hbd

/-- A balanced edge with at least one branching endpoint is reconstructed
from the branch multisets at the unique centroids of the leaf cards. -/
theorem recover_nonunary {a b c d : Shape}
    (hab : order a = order b) (hac : order a = order c) (had : order a = order d)
    (ha : 2 ≤ order a) (hbranch : 2 ≤ (children a).card ∨ 2 ≤ (children b).card)
    (h : cards a b = cards c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have move {a b c d : Shape} (hab : order a = order b) (hac : order a = order c)
      (had : order a = order d) (ha : 2 ≤ order a) (han : 2 ≤ (children a).card)
      (h : cards a b = cards c d) :
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
    rcases matches_nonunary hab hac had ha han h with hcase|hcase
    · subst c
      exact Or.inl ⟨rfl,recover_with_fixed_nonunary hab had ha han h⟩
    · subst d
      exact Or.inr ⟨rfl,recover_with_fixed_nonunary hab hac ha han (h.trans (cards_comm c a))⟩
  rcases hbranch with han|hbn
  · exact move hab hac had ha han h
  · have hm := move hab.symm (hab.symm.trans hac) (hab.symm.trans had) (hab ▸ ha) hbn
      ((cards_comm b a).trans h)
    exact hm.elim (fun q => Or.inr ⟨q.2,q.1⟩) (fun q => Or.inl ⟨q.2,q.1⟩)

end EvenCentroidProfile

namespace TreeHalf

open SimpleGraph TreeCentroid TreeBranches FiniteRootedTree RootedClass

section EvenCards

variable {V : Type} [Finite V] {G : SimpleGraph V}

private abbrev arbitraryRoot (G : SimpleGraph V) (hG : G.IsTree) (r : V) : Tree :=
  ⟨V,G,r,hG,inferInstance⟩

private theorem branchList_single_le {T : Tree} {C : Branch T.G T.r} :
    branchClass T C ∈ branchMultiset T := by
  classical
  unfold branchMultiset
  exact Multiset.mem_map.mpr ⟨C,by simp,rfl⟩

private theorem even_leaf_data (hG : G.IsTree) {r z : V} (h : G.Adj r z) {k : ℕ}
    (hk : Nat.card V = 2*k) (h₁ : order (halfClass hG h) = k)
    (h₂ : order (halfClass hG h.symm) = k)
    {l : V} (hr : r ≠ l) (hz : z ≠ l) (hl : IsLeaf (arbitraryRoot G hG r) l)
    (hi : l ∈ cut h) :
    let T := leafCard (arbitraryRoot G hG r) l hr hl
    let X := ofTree (leafCard (half hG h) ⟨l,hi⟩ (fun he => hz (congrArg Subtype.val he))
      (leafHalfIn hG h hz hl hi))
    balanced T.G T.r 0 ∧ branchMultiset T = X ::ₘ children (halfClass hG h.symm) := by
  let T := leafCard (arbitraryRoot G hG r) l hr hl
  let X := ofTree (leafCard (half hG h) ⟨l,hi⟩ (fun he => hz (congrArg Subtype.val he))
    (leafHalfIn hG h hz hl hi))
  have hout : l ∉ cut h.symm := by rw [cut_symm hG h]; exact fun he => he hi
  have hin := halfClass_leaf_in hG h hr hz hl hi
  have ho := halfClass_leaf_out hG h.symm hz hr (show IsLeaf (arbitraryRoot G hG z) l from hl) hout
  have he := branchMultiset_split_half T.connected (edgeOnCard h hr hz)
  have he' : branchMultiset T = X ::ₘ children (halfClass hG h.symm) := by
    change branchMultiset T = halfClass T.connected (edgeOnCard h hr hz) ::ₘ
      children (halfClass T.connected (edgeOnCard h hr hz).symm) at he
    exact he.trans (congrArg₂ (· ::ₘ ·) hin (congrArg children ho))
  refine ⟨?_,he'⟩
  intro C
  have hh := branchList_single_le (T := T) (C := C)
  rw [he',Multiset.mem_cons] at hh
  have ho' : order X + 1 = k := (order_leafCard _ _ _ _).trans h₁
  have hn := order_leafCard (arbitraryRoot G hG r) l hr hl
  change Nat.card (Deleted l) + 1 = Nat.card V at hn
  change 2 * order (branchClass T C) + 0 < Nat.card (Deleted l)
  rcases hh with hHead|hTail
  · rw [hHead]
    omega
  · have hlt := child_order_lt hTail
    omega

/-- The family of leaf-card branch multisets at strictly balanced centroids. -/
def centroidProfiles (G : SimpleGraph V) (hG : G.IsTree) : Set (Multiset FiniteRootedTree.Class) :=
  {m | ∃ (l : V) (c : Deleted l)
      (hl : IsLeaf (arbitraryRoot G hG c.val) l),
    let T := leafCard (arbitraryRoot G hG c.val) l c.property hl
    balanced T.G T.r 0 ∧ branchMultiset T = m}

theorem centroidProfiles_even (hG : G.IsTree) {r z : V} (h : G.Adj r z) {k : ℕ}
    (hk : Nat.card V = 2*k) (hmin : 2 ≤ k) (h₁ : order (halfClass hG h) = k)
    (h₂ : order (halfClass hG h.symm) = k) :
    centroidProfiles G hG = EvenCentroidProfile.cards (halfClass hG h.symm) (halfClass hG h) := by
  classical
  have classify (r z : V) (h : G.Adj r z) (h₁ : order (halfClass hG h) = k)
      (h₂ : order (halfClass hG h.symm) = k)
      (l : V) (c : Deleted l) (hl : IsLeaf (arbitraryRoot G hG c.val) l)
      (hb : balanced (cardAt G l) c 0) (hi : l ∈ cut h) :
      branchMultiset (leafCard (arbitraryRoot G hG c.val) l c.property hl) ∈
        EvenCentroidProfile.one (halfClass hG h.symm) (halfClass hG h) := by
    have hr : r ≠ l := fun hh => root_not_branchVerts (toward h) (hh.symm ▸ hi)
    have hz : z ≠ l := fun hh => edge_end_not_leaf hG h (h₁.symm ▸ hmin) (hh.symm ▸ hl)
    let T := leafCard (arbitraryRoot G hG r) l hr hl
    have hx := even_leaf_data hG h hk h₁ h₂ hr hz hl hi
    have he : c = T.r := balanced_unique T.connected hb hx.1
    have hev : c.val = r := congrArg (fun x : Deleted l => x.val) he
    subst r
    refine ⟨_,?_,hx.2.symm⟩
    exact (trim_some_ofTree_iff _ _).mpr ⟨⟨l,hi⟩,_,_,rfl⟩
  have realize (r z : V) (h : G.Adj r z) (h₁ : order (halfClass hG h) = k)
      (h₂ : order (halfClass hG h.symm) = k) {m : Multiset FiniteRootedTree.Class}
      (hm : m ∈ EvenCentroidProfile.one (halfClass hG h.symm) (halfClass hG h)) :
      m ∈ centroidProfiles G hG := by
    obtain ⟨x,hx,rfl⟩ := hm
    obtain ⟨l,hn,hl,hx'⟩ := (trim_some_ofTree_iff (half hG h) x).mp hx
    have hr : r ≠ l.val := fun he => root_not_branchVerts (toward h)
      (Eq.mp (congrArg (fun x => x ∈ cut h) he.symm) l.property)
    have hz : z ≠ l.val := fun he => hn (Subtype.ext he)
    have hL := (leaf_half_iff hG h l hz.symm).mp hl
    have hd := even_leaf_data hG h hk h₁ h₂ hr hz hL l.property
    exact ⟨l.val,newRoot hr,hL,hd.1,hd.2.trans (congrArg (· ::ₘ children (halfClass hG h.symm)) hx')⟩
  ext m
  constructor
  · rintro ⟨l,c,hl,hb,rfl⟩
    by_cases hi : l ∈ cut h
    · exact Or.inl (classify r z h h₁ h₂ l c hl hb hi)
    · have hi' : l ∈ cut h.symm := by rwa [cut_symm hG h]
      exact Or.inr (classify z r h.symm h₂ h₁ l c hl hb hi')
  · intro hm
    rcases hm with hm|hm
    · exact realize r z h h₁ h₂ hm
    · exact realize z r h.symm h₂ h₁ hm

end EvenCards

section Further

variable {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

theorem centroidProfiles_hypomorphic (hV : 3 ≤ Fintype.card V) (hG : G.IsTree)
    (h : ReconstructionConjecture.Hypomorphic G H) (hH : H.IsTree) :
    centroidProfiles G hG = centroidProfiles H hH := by
  obtain ⟨σ,hσ,hdegree⟩ := TreeReconstruction.degree_preserving_hypomorphism hV h
  have transport {A B : Type} [Finite A] [Finite B] {X : SimpleGraph A} {Y : SimpleGraph B}
      (hX : X.IsTree) (hY : Y.IsTree) (l : A) (l' : B) (e : cardAt X l ≃g cardAt Y l')
      (hd : Nat.card (X.neighborSet l) = Nat.card (Y.neighborSet l')) (c : Deleted l)
      (hl : IsLeaf (arbitraryRoot X hX c.val) l)
      (hb : balanced (cardAt X l) c 0) :
      branchMultiset (leafCard (arbitraryRoot X hX c.val) l c.property hl) ∈
        centroidProfiles Y hY := by
    have hl' : IsLeaf (arbitraryRoot Y hY (e c).val) l' := by
      rw [leaf_iff_card_neighbor] at hl ⊢
      exact hd.symm.trans hl
    refine ⟨l',e c,hl',balanced_iso e hb,?_⟩
    exact (branchMultiset_related ⟨e,rfl⟩).symm
  ext m
  constructor
  · rintro ⟨l,c,hl,hb,rfl⟩
    exact transport hG hH l (σ l) (hσ l).some (hdegree l) c hl hb
  · rintro ⟨l',c,hl,hb,rfl⟩
    obtain ⟨l,rfl⟩ := σ.surjective l'
    exact transport hH hG (σ l) l (hσ l).some.symm (hdegree l).symm c hl hb

omit [Fintype V] [Fintype W] in
theorem isCentroid_congr {r : V} {s : W}
    (hcard : Nat.card V = Nat.card W) (e : cardAt G r ≃g cardAt H s) :
    isCentroid G r → isCentroid H s := by
  intro h D
  obtain ⟨C,rfl⟩ := e.connectedComponentEquiv.surjective D
  rw [← Nat.card_congr (C.isoEquivSupp e),← hcard]
  exact h C

end Further

end TreeHalf

namespace RootedClass

open FiniteRootedTree Multiset

abbrev Shape := FiniteRootedTree.Class

theorem order_of_single_child {a u : Shape} (h : children a = {u}) : order a = order u + 1 := by
  rw [order_eq_children_sum,h]
  simp [Nat.add_comm]

theorem children_eq_zero_of_order_eq_one {a : Shape} (h : order a = 1) :
    children a = 0 := by
  by_contra hn
  have hc : 0 < (children a).card := Multiset.card_pos.mpr hn
  obtain ⟨u,hu⟩ := Multiset.card_pos_iff_exists_mem.mp hc
  have ht := child_order_lt hu
  have hp := order_pos u
  omega

noncomputable def unaryDepth (a : Shape) : ℕ := by
  classical
  exact if h : ∃ u, children a = {u} then unaryDepth (Classical.choose h) + 1 else 0
termination_by order a
decreasing_by
  let u := Classical.choose h
  have hu : children a = {u} := Classical.choose_spec h
  exact child_order_lt (show u ∈ children a from hu.symm ▸ (by simp : u ∈ ({u} : Multiset Shape)))

theorem unaryDepth_cons {a u : Shape} (h : children a = {u}) :
    unaryDepth a = unaryDepth u + 1 := by
  classical
  have he : ∃ u, children a = {u} := ⟨u,h⟩
  rw [unaryDepth,dif_pos he]
  have hx := (Classical.choose_spec he).symm.trans h
  rw [Multiset.singleton_inj.mp hx]

theorem unaryDepth_zero {a : Shape} (h : ¬∃ u, children a = {u}) :
    unaryDepth a = 0 := by
  classical
  rw [unaryDepth,dif_neg h]

def IsChain (a : Shape) : Prop := unaryDepth a + 1 = order a

theorem unaryDepth_bound (a : Shape) : unaryDepth a + 1 ≤ order a := by
  classical
  by_cases h : ∃ u, children a = {u}
  · obtain ⟨u,hu⟩ := h
    have ht := unaryDepth_bound u
    rw [unaryDepth_cons hu,order_of_single_child hu]
    omega
  · rw [unaryDepth_zero h]
    exact order_pos a
termination_by order a
decreasing_by
  exact child_order_lt (by rw [hu]; simp)

theorem chain_of_order_one {a : Shape} (h : order a = 1) : IsChain a := by
  have hb := unaryDepth_bound a
  unfold IsChain
  omega

theorem chain_iff_child {a u : Shape} (h : children a = {u}) :
    IsChain a ↔ IsChain u := by
  unfold IsChain
  rw [unaryDepth_cons h,order_of_single_child h]
  omega

theorem chain_unique {a b : Shape} (ha : IsChain a) (hb : IsChain b)
    (h : order a = order b) : a = b := by
  classical
  by_cases hs : order a = 1
  · exact children_injective ((children_eq_zero_of_order_eq_one hs).trans
      (children_eq_zero_of_order_eq_one (h.symm.trans hs)).symm)
  have aux (u : Shape) (hu : IsChain u) (hu' : order u ≠ 1) : ∃ v, children u = {v} := by
    by_contra hh
    have hz := unaryDepth_zero hh
    exact hu' (by simpa only [IsChain,hz,zero_add] using hu.symm)
  obtain ⟨u,hu⟩ := aux a ha hs
  obtain ⟨v,hv⟩ := aux b hb (fun hh => hs (h.trans hh))
  have hn : order u = order v := by
    have h₁ := order_of_single_child hu
    have h₂ := order_of_single_child hv
    omega
  have he := chain_unique ((chain_iff_child hu).mp ha) ((chain_iff_child hv).mp hb) hn
  exact children_injective (hu.trans (by simpa [he] using hv.symm))
termination_by order a
decreasing_by
  exact child_order_lt (by rw [hu]; simp)

private theorem remaining_trim_at_only_child {a b u : Shape}
    (h : b ∈ trims a) (hu : children a = {u}) :
    ∃ z, trim u z ∧ children b = RootedBranchDeck.insertOption z 0 := by
  obtain ⟨x,z,r,hh,ht,hr⟩ := trim_children h
  have hzero : r.card = 0 := by
    have hc := congrArg Multiset.card (hu.symm.trans hh)
    change ({u} : Multiset Shape).card = (x ::ₘ r).card at hc
    simp only [Multiset.card_singleton,Multiset.card_cons] at hc
    omega
  have hz : r = 0 := Multiset.card_eq_zero.mp hzero
  subst r
  have he : u = x := Multiset.singleton_inj.mp (hu.symm.trans hh)
  subst x
  exact ⟨z,ht,hr⟩

theorem trim_unaryDepth {a b : Shape} (h : b ∈ trims a) :
    (IsChain a → IsChain b) ∧ (¬IsChain a → unaryDepth a ≤ unaryDepth b) := by
  classical
  by_cases hu : ∃ u, children a = {u}
  · obtain ⟨u,hu⟩ := hu
    obtain ⟨z,hz,he⟩ := remaining_trim_at_only_child h hu
    cases z with
    | none =>
      have hs : order u = 1 := hz
      have hb := trim_order h
      have ha := order_of_single_child hu
      have h₁ := (chain_iff_child hu).mpr (chain_of_order_one hs)
      exact ⟨fun _ => chain_of_order_one (by omega),fun hn => (hn h₁).elim⟩
    | some v =>
      have hv : children b = {v} := he
      have hi := trim_unaryDepth (show v ∈ trims u from hz)
      refine ⟨?_ , ?_⟩
      · intro hchain
        exact (chain_iff_child hv).mpr (hi.1 ((chain_iff_child hu).mp hchain))
      · intro hn
        have hnu := (not_congr (chain_iff_child hu)).mp hn
        rw [unaryDepth_cons hu,unaryDepth_cons hv]
        exact Nat.add_le_add_right (hi.2 hnu) _
  · have hzero := unaryDepth_zero hu
    have hs := trim_order h
    have hpos := order_pos b
    have hno : ¬IsChain a := fun hh => by unfold IsChain at hh; omega
    exact ⟨fun hh => (hno hh).elim,fun _ => hzero ▸ Nat.zero_le _⟩
termination_by order a
decreasing_by
  exact child_order_lt (by rw [hu]; simp)

/-- The possible trims of a tree with one branch of the given type. -/
def unaryTrims (u : Shape) : Set Shape :=
  {z | ∃ a, children a = {u} ∧ z ∈ trims a}

theorem unaryTrims_nonempty {a u : Shape} (h : children a = {u}) : (unaryTrims u).Nonempty := by
  have ho := order_of_single_child h
  have hpos := order_pos u
  obtain ⟨x,hx⟩ := trims_nonempty (a := a) (by omega)
  exact ⟨x,a,h,hx⟩

theorem unaryTrim_order {a b : Shape} (h : b ∈ unaryTrims a) : order b = order a := by
  obtain ⟨u,hu,hz⟩ := h
  have ho := order_of_single_child hu
  have hzo := trim_order hz
  omega

theorem unaryTrim_growth {a b : Shape} (h : b ∈ unaryTrims a) :
    (IsChain a ∧ b = a) ∨ unaryDepth a < unaryDepth b := by
  obtain ⟨u,hu,ht⟩ := h
  have hord := unaryTrim_order (show b ∈ unaryTrims a from ⟨u,hu,ht⟩)
  obtain ⟨x,hx,he⟩ := remaining_trim_at_only_child ht hu
  cases x with
  | none =>
    have h₁ := chain_of_order_one (show order a = 1 from hx)
    have h₂ := chain_of_order_one (hord.trans (show order a = 1 from hx))
    exact Or.inl ⟨h₁,chain_unique h₂ h₁ hord⟩
  | some x =>
    have hs : children b = {x} := he
    have hi := trim_unaryDepth (show x ∈ trims a from hx)
    by_cases hchain : IsChain a
    · exact Or.inl ⟨hchain,chain_unique ((chain_iff_child hs).mpr (hi.1 hchain)) hchain hord⟩
    · exact Or.inr (by rw [unaryDepth_cons hs]; have hle := hi.2 hchain; omega)

end RootedClass

namespace RootedClass

open FiniteRootedTree Multiset

theorem trims_eq_unaryTrims {a u : Shape} (h : children a = {u}) :
    trims a = unaryTrims u := by
  ext z
  constructor
  · exact fun hz => ⟨a,h,hz⟩
  · rintro ⟨b,hb,hz⟩
    exact (children_injective (hb.trans h.symm)) ▸ hz

private theorem recover_minimum_unary {a b c d : Shape}
    (hab : order a = order b) (hac : order a = order c) (had : order a = order d)
    (hba : unaryDepth a ≤ unaryDepth b) (hca : unaryDepth a ≤ unaryDepth c)
    (hda : unaryDepth a ≤ unaryDepth d)
    (hea : (unaryTrims a).Nonempty) (heb : (unaryTrims b).Nonempty)
    (he : CentroidPairDeck.twoSides unaryTrims a b = CentroidPairDeck.twoSides unaryTrims c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  by_cases hchain : IsChain a
  · have hc : IsChain c := by
      have hn := unaryDepth_bound c
      unfold IsChain at hchain ⊢
      omega
    have hb : IsChain b := by
      have hn := unaryDepth_bound b
      unfold IsChain at hchain ⊢
      omega
    have hd : IsChain d := by
      have hn := unaryDepth_bound d
      unfold IsChain at hchain ⊢
      omega
    exact Or.inl ⟨chain_unique hchain hc hac,chain_unique hb hd (hab.symm.trans had)⟩
  have hno : a ∉ unaryTrims a := by
    intro htrim
    rcases unaryTrim_growth htrim with hcase|hcase
    · exact hchain hcase.1
    · omega
  obtain ⟨x,hx⟩ := heb
  have hm : ({a,x} : Multiset Shape) ∈ CentroidPairDeck.twoSides unaryTrims c d :=
    he ▸ Or.inl ⟨x,hx,rfl⟩
  have findSide {u v : Shape} (hmin : unaryDepth a ≤ unaryDepth v)
      (hm : ({a,x} : Multiset Shape) ∈ CentroidPairDeck.oneSide u (unaryTrims v)) :
      a = u ∨ a = v := by
    obtain ⟨y,hy,hpair⟩ := hm
    change ({u,y} : Multiset Shape) = {a,x} at hpair
    have hm : a ∈ ({u,y} : Multiset Shape) := by rw [hpair]; simp
    change a ∈ u ::ₘ ({y} : Multiset Shape) at hm
    have hem : a = u ∨ a = y := by simpa only [Multiset.mem_cons,Multiset.mem_singleton] using hm
    rcases hem with hp|hp
    · exact Or.inl hp
    · subst y
      rcases unaryTrim_growth hy with hstay|hnext
      · exact Or.inr hstay.2
      · omega
  have hmatch := hm.elim (findSide hda) (fun hp => (findSide hca hp).symm)
  rcases hmatch with heq|heq
  · subst c
    exact Or.inl ⟨rfl,CentroidPairDeck.twoSides_eq_fixed_branch hno hea he⟩
  · subst d
    exact Or.inr ⟨rfl,CentroidPairDeck.twoSides_eq_fixed_branch hno hea
      (he.trans (Set.union_comm _ _))⟩

theorem recover_unary_pairs {a b c d : Shape}
    (hab : order a = order b) (hac : order a = order c) (had : order a = order d)
    (ha : (unaryTrims a).Nonempty) (hb : (unaryTrims b).Nonempty)
    (hc : (unaryTrims c).Nonempty) (hd : (unaryTrims d).Nonempty)
    (he : CentroidPairDeck.twoSides unaryTrims a b = CentroidPairDeck.twoSides unaryTrims c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  let S : Finset Shape := {a,b,c,d}
  obtain ⟨x,hx,hmin⟩ := Finset.exists_min_image S unaryDepth ⟨a,by simp [S]⟩
  have e : x = a ∨ x = b ∨ x = c ∨ x = d := by simpa [S] using hx
  have ha' := hmin a (by simp [S])
  have hb' := hmin b (by simp [S])
  have hc' := hmin c (by simp [S])
  have hd' := hmin d (by simp [S])
  rcases e with rfl|rfl|rfl|rfl
  · exact recover_minimum_unary hab hac had hb' hc' hd' ha hb he
  · have hm := recover_minimum_unary hab.symm (hab.symm.trans hac) (hab.symm.trans had)
      ha' hc' hd' hb ha ((Set.union_comm _ _).trans he)
    exact hm.elim (fun q => Or.inr ⟨q.2,q.1⟩) (fun q => Or.inl ⟨q.2,q.1⟩)
  · have hm := recover_minimum_unary (hac.symm.trans had) hac.symm (hac.symm.trans hab)
      hd' ha' hb' hc hd he.symm
    exact hm.elim (fun q => Or.inl ⟨q.1.symm,q.2.symm⟩) (fun q => Or.inr ⟨q.2.symm,q.1.symm⟩)
  · have hm := recover_minimum_unary (had.symm.trans hac) had.symm (had.symm.trans hab)
      hc' ha' hb' hd hc ((Set.union_comm _ _).trans he.symm)
    exact hm.elim (fun q => Or.inr ⟨q.1.symm,q.2.symm⟩) (fun q => Or.inl ⟨q.2.symm,q.1.symm⟩)

end RootedClass

namespace EvenCentroidProfile

open FiniteRootedTree RootedClass Multiset

private theorem unary_card_profile {a b x y : Shape} (ha : children a = {x})
    (hb : children b = {y}) : cards a b = CentroidPairDeck.twoSides unaryTrims x y := by
  have aux {a b x y : Shape} (ha : children a = {x}) (hb : children b = {y}) :
      one a b = CentroidPairDeck.oneSide x (unaryTrims y) := by
    unfold one CentroidPairDeck.oneSide
    rw [ha,trims_eq_unaryTrims hb]
    exact Set.image_congr (fun z _ => Multiset.cons_swap z x 0)
  unfold cards CentroidPairDeck.twoSides
  rw [aux ha hb,aux hb ha]

theorem recover {a b c d : Shape}
    (hab : order a = order b) (hac : order a = order c) (had : order a = order d)
    (ha : 2 ≤ order a) (h : cards a b = cards c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  by_cases hbranch : 2 ≤ (children a).card ∨ 2 ≤ (children b).card
  · exact recover_nonunary hab hac had ha hbranch h
  have hp {u : Shape} (hord : order a = order u) (hbound : ¬ 2 ≤ (children u).card) :
      (children u).card = 1 := by
    have hh := children_nonempty (hord ▸ ha)
    omega
  have hs := not_or.mp hbranch
  have hcBound : ¬ 2 ≤ (children c).card := by
    intro hc
    have hm := matches_nonunary (hac.symm.trans had) hac.symm (hac.symm.trans hab)
      (hac ▸ ha) hc h.symm
    rcases hm with hm|hm <;> simp_all
  have hdBound : ¬ 2 ≤ (children d).card := by
    intro hd
    have hm := matches_nonunary (had.symm.trans hac) had.symm (had.symm.trans hab)
      (had ▸ ha) hd ((cards_comm d c).trans h.symm)
    rcases hm with hm|hm <;> simp_all
  obtain ⟨u,hu⟩ := Multiset.card_eq_one.mp (hp rfl hs.1)
  obtain ⟨v,hv⟩ := Multiset.card_eq_one.mp (hp hab hs.2)
  obtain ⟨w,hw⟩ := Multiset.card_eq_one.mp (hp hac hcBound)
  obtain ⟨x,hx⟩ := Multiset.card_eq_one.mp (hp had hdBound)
  have h1 := order_of_single_child hu
  have h2 := order_of_single_child hv
  have h3 := order_of_single_child hw
  have h4 := order_of_single_child hx
  rw [unary_card_profile hu hv,unary_card_profile hw hx] at h
  have he := recover_unary_pairs (by omega) (by omega) (by omega)
    (unaryTrims_nonempty hu) (unaryTrims_nonempty hv)
    (unaryTrims_nonempty hw) (unaryTrims_nonempty hx) h
  rcases he with ⟨huw,hvx⟩|⟨hux,hvw⟩
  · exact Or.inl ⟨children_injective (hu.trans (by simpa [huw] using hw.symm)),
      children_injective (hv.trans (by simpa [hvx] using hx.symm))⟩
  · exact Or.inr ⟨children_injective (hu.trans (by simpa [hux] using hx.symm)),
      children_injective (hv.trans (by simpa [hvw] using hw.symm))⟩

end EvenCentroidProfile

namespace TreeHalf

open SimpleGraph TreeCentroid TreeBranches FiniteRootedTree RootedClass ReconstructionConjecture

theorem order_of_two_centroids {V : Type} [Finite V] {G : SimpleGraph V}
    (hG : G.IsTree) {r z : V} (h : G.Adj r z)
    (hr : isCentroid G r) (hz : isCentroid G z) :
    2 * order (halfClass hG h) = Nat.card V := by
  have h₁ : 2 * order (halfClass hG h) ≤ Nat.card V := by
    rw [halfClass_eq_branch hG h]
    exact hr (toward h)
  have h₂ : 2 * order (halfClass hG h.symm) ≤ Nat.card V := by
    rw [halfClass_eq_branch hG h.symm]
    exact hz (toward h.symm)
  have hs := opposite_half_order hG h
  omega

/-- Trees of even order are reconstructible from their vertex decks. -/
theorem reconstruct_even {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (hV : 3 ≤ Fintype.card V)
    (hG : G.IsTree) (h : Hypomorphic G H) (he : Even (Nat.card V)) :
    Nonempty (G ≃g H) := by
  classical
  obtain ⟨r,hr⟩ := exists_centroid hG
  by_cases hr' : ∀ z, isCentroid G z → z = r
  · exact reconstruct_even_unique_centroid hV hG h he ⟨r,hr,hr'⟩
  push Not at hr'
  obtain ⟨z,hz,hn⟩ := hr'
  have hz' := (second_centroid_adj hG (Ne.symm hn) hr hz).1
  have hH := TreeReconstruction.tree_of_hypomorphic hV hG h
  have hc : Nat.card V = Nat.card W := by simpa only [Nat.card_eq_fintype_card] using h.card_eq
  have hc₃ : 3 ≤ Nat.card V := by simpa only [Nat.card_eq_fintype_card] using hV
  have hprof := centroidProfiles_hypomorphic hV hG h hH
  obtain ⟨σ,hσ⟩ := h
  have hs : isCentroid H (σ r) := isCentroid_congr hc (hσ r).some hr
  have hw : isCentroid H (σ z) := isCentroid_congr hc (hσ z).some hz
  have hj : H.Adj (σ r) (σ z) := (second_centroid_adj hH (σ.injective.ne hn.symm) hs hw).1
  let k := order (halfClass hG hz')
  have hk : Nat.card V = 2*k := (order_of_two_centroids hG hz' hr hz).symm
  have hk' : Nat.card W = 2*k := hc.symm.trans hk
  have hk₂ : 2 ≤ k := by omega
  have hrev : order (halfClass hG hz'.symm) = k := by
    have hs := order_of_two_centroids hG hz'.symm hz hr
    omega
  have hj₁ : order (halfClass hH hj) = k := by
    have hs := order_of_two_centroids hH hj hs hw
    omega
  have hj₂ : order (halfClass hH hj.symm) = k := by
    have hs := order_of_two_centroids hH hj.symm hw hs
    omega
  rw [centroidProfiles_even hG hz' hk hk₂ rfl hrev,
    centroidProfiles_even hH hj hk' hk₂ hj₁ hj₂] at hprof
  rcases EvenCentroidProfile.recover hrev (hrev.trans hj₂.symm) (hrev.trans hj₁.symm)
    (hrev.symm ▸ hk₂) hprof with hh|hh
  · exact assemble hG hH hz' hj hh.2 hh.1
  · exact assemble hG hH hz' hj.symm hh.2 hh.1

end TreeHalf

namespace TreeHalf

open SimpleGraph TreeCentroid TreeBranches FiniteRootedTree RootedClass ReconstructionConjecture

theorem toward_attachment {V : Type} {G : SimpleGraph V} (hG : G.IsTree) {r : V}
    (C : Branch G r) : toward (adj_attachment hG C) = C :=
  (attachment hG C).property

theorem cut_disjoint {V : Type} {G : SimpleGraph V} {r z w : V} (h : G.Adj r z) (h' : G.Adj r w)
    (hneq : toward h ≠ toward h') : Disjoint (cut h) (cut h') := by
  apply Set.disjoint_left.mpr
  rintro x ⟨y,hy⟩ ⟨u,hu⟩
  have hs : y.val = u.val := Subtype.ext (hy.trans hu.symm)
  have he : (cardAt G r).connectedComponentMk y.val = toward h := y.property
  rw [hs] at he
  exact hneq (he.symm.trans u.property)

theorem centroid_other_unique {V : Type} [Finite V] {G : SimpleGraph V}
    (hG : G.IsTree) {r z w : V} (hr : isCentroid G r)
    (hz : isCentroid G z) (hw : isCentroid G w) (hnz : r ≠ z) (hnw : r ≠ w) : z = w := by
  have hz' := (second_centroid_adj hG hnz hr hz).1
  have hw' := (second_centroid_adj hG hnw hr hw).1
  by_contra hneq
  have hcz : 2 * Nat.card (toward hz').supp = Nat.card V := by
    have hh := order_of_two_centroids hG hz' hr hz
    rwa [halfClass_eq_branch hG hz'] at hh
  have hcw : 2 * Nat.card (toward hw').supp = Nat.card V := by
    have hh := order_of_two_centroids hG hw' hr hw
    rwa [halfClass_eq_branch hG hw'] at hh
  have htt : toward hz' ≠ toward hw' := by
    intro heq
    apply hneq
    have ha := congrArg (fun C => (attachment hG C).val.val) heq
    simpa only [attachment_toward hG hz',attachment_toward hG hw'] using ha
  have hp := other_branch_le htt
  omega

theorem centroid_strict_no_other {V : Type} [Finite V] {G : SimpleGraph V} {r z : V}
    (hG : G.IsTree) (hr : balanced G r 0) (hz : isCentroid G z) : r = z := by
  by_contra he
  have hra : isCentroid G r := fun C => by have hC := hr C; omega
  obtain ⟨_,C,hC⟩ := second_centroid_adj hG he hra hz
  have hc := hr C
  omega

theorem halfClass_iso {V W : Type} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.IsTree) (hH : H.IsTree) (e : G ≃g H) {r z : V} (h : G.Adj r z) :
    halfClass hG h = halfClass hH (e.map_adj_iff.mpr h) := by
  let h' := e.map_adj_iff.mpr h
  let f := FiniteRootedTree.deletedIso (r := r) e rfl
  have hm (x : V) : x ∈ cut h ↔ e x ∈ cut h' := by
    rw [mem_cut_iff,mem_cut_iff]
    constructor
    · rintro ⟨hx,hh⟩
      exact ⟨e.injective.ne hx,hh.map f.toHom⟩
    · rintro ⟨hx,hh⟩
      have hr := e.injective.ne_iff.mp hx
      have hs : (cardAt H (e r)).Reachable (f ⟨z,h.ne'⟩) (f ⟨x,hr⟩) := hh
      exact ⟨hr,f.reachable_iff.mp hs⟩
  let q : G.induce (cut h) ≃g H.induce (cut h') :=
    { toEquiv := {
      toFun := fun x => ⟨e x.val,(hm x.val).mp x.property⟩
      invFun := fun x => ⟨e.symm x.val,(hm _).mpr (by rw [e.apply_symm_apply]; exact x.property)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val) }
      map_rel_iff' := e.map_rel_iff }
  exact ofTree_eq_iff.mpr ⟨q,rfl⟩

private theorem centroid_iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {r : V} (hr : isCentroid G r) : isCentroid H (e r) :=
  isCentroid_congr (Nat.card_congr e.toEquiv) (FiniteRootedTree.deletedIso e rfl) hr

/-- The unordered rooted halves of leaf cards that have two centroids. -/
def pairProfiles {V : Type} [Finite V] (G : SimpleGraph V) (hG : G.IsTree) :
    Set (Multiset FiniteRootedTree.Class) :=
  {m | ∃ (l : V) (c d : Deleted l) (hl : IsLeaf (arbitraryRoot G hG c.val) l)
      (h : (cardAt G l).Adj c d),
    let T := leafCard (arbitraryRoot G hG c.val) l c.property hl
    isCentroid T.G c ∧ isCentroid T.G d ∧
      m = {halfClass T.connected h,halfClass T.connected h.symm}}

theorem pairProfiles_hypomorphic {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (hV : 3 ≤ Fintype.card V) (hG : G.IsTree)
    (h : Hypomorphic G H) (hH : H.IsTree) : pairProfiles G hG = pairProfiles H hH := by
  obtain ⟨σ,hσ,hd⟩ := TreeReconstruction.degree_preserving_hypomorphism hV h
  have transport {A B : Type} [Finite A] [Finite B] {X : SimpleGraph A} {Y : SimpleGraph B}
      (hX : X.IsTree) (hY : Y.IsTree) (l : A) (l' : B) (e : cardAt X l ≃g cardAt Y l')
      (hdeg : Nat.card (X.neighborSet l) = Nat.card (Y.neighborSet l'))
      (c d : Deleted l) (hl : IsLeaf (arbitraryRoot X hX c.val) l)
      (hadj : (cardAt X l).Adj c d) (hc : isCentroid (cardAt X l) c)
      (hc' : isCentroid (cardAt X l) d) :
      let T := leafCard (arbitraryRoot X hX c.val) l c.property hl
      ({halfClass T.connected hadj,halfClass T.connected hadj.symm}
        : Multiset FiniteRootedTree.Class) ∈ pairProfiles Y hY := by
    let T := leafCard (arbitraryRoot X hX c.val) l c.property hl
    have hl' : IsLeaf (arbitraryRoot Y hY (e c).val) l' := by
      rw [leaf_iff_card_neighbor] at hl ⊢
      exact hdeg.symm.trans hl
    let U := leafCard (arbitraryRoot Y hY (e c).val) l' (e c).property hl'
    let h₀ := e.map_adj_iff.mpr hadj
    refine ⟨l',e c,e d,hl',h₀,centroid_iso e hc,centroid_iso e hc',?_⟩
    have h₁ := halfClass_iso T.connected U.connected e hadj
    have h₂ := halfClass_iso T.connected U.connected e hadj.symm
    rw [h₁,h₂]
  ext m
  constructor
  · rintro ⟨l,c,d,hl,hadj,hc,hc',rfl⟩
    exact transport hG hH l (σ l) (hσ l).some (hd l) c d hl hadj hc hc'
  · rintro ⟨l',c,d,hl,hadj,hc,hc',rfl⟩
    obtain ⟨l,rfl⟩ := σ.surjective l'
    exact transport hH hG (σ l) l (hσ l).some.symm (hd l).symm c d hl hadj hc hc'

end TreeHalf

namespace TreeHalf

open SimpleGraph TreeCentroid TreeBranches FiniteRootedTree RootedClass

private theorem centroid_of_equal_halves {V : Type} [Finite V] {G : SimpleGraph V}
    (hG : G.IsTree) {r z : V} (h : G.Adj r z)
    (hn : 2 * order (halfClass hG h) = Nat.card V)
    (hn' : order (halfClass hG h.symm) = order (halfClass hG h)) : isCentroid G r := by
  intro C
  let T := arbitraryRoot G hG r
  have hh := branchList_single_le (T := T) (C := C)
  rw [branchMultiset_split_half hG h,Multiset.mem_cons] at hh
  change 2 * order (branchClass T C) ≤ Nat.card V
  rcases hh with hh|hh
  · rw [hh,hn]
  · have hl := child_order_lt (show branchClass T C ∈ children (halfClass hG h.symm) from hh)
    omega

private theorem balancedFromCard {V : Type} [Finite V] {G : SimpleGraph V}
    (hG : G.IsTree) {r z : V} (h : G.Adj r z) {k : ℕ}
    (hk : Nat.card V = 2*k) (hsmall : order (halfClass hG h) < k)
    (hRest : ∀ x ∈ children (halfClass hG h.symm), order x < k) :
    balanced G r 0 := by
  intro C
  let T := arbitraryRoot G hG r
  have hh := branchList_single_le (T := T) (C := C)
  rw [branchMultiset_split_half hG h,Multiset.mem_cons] at hh
  change 2 * order (branchClass T C) + 0 < Nat.card V
  rcases hh with he|hm
  · rw [he]
    omega
  · have ho := hRest _ hm
    omega

section OddCards

variable {V : Type} [Finite V] {G : SimpleGraph V} (hG : G.IsTree)
variable {r z : V} (h : G.Adj r z) {k : ℕ}
variable (hk : Nat.card V = 2*k+1) (hA : order (halfClass hG h) = k)

include hk hA in
private theorem odd_other_order : order (halfClass hG h.symm) = k+1 := by
  have hh := opposite_half_order hG h
  omega

include hk hA in
private theorem both_centroids_of_outside_leaf {l : V} (hr : r ≠ l) (hz : z ≠ l)
    (hl : IsLeaf (arbitraryRoot G hG r) l) (hout : l ∉ cut h) :
    let T := leafCard (arbitraryRoot G hG r) l hr hl
    isCentroid T.G (newRoot hr) ∧ isCentroid T.G (newRoot hz) := by
  let T := leafCard (arbitraryRoot G hG r) l hr hl
  let h' := edgeOnCard h hr hz
  have hin : l ∈ cut h.symm := by rwa [cut_symm hG h]
  have hper : halfClass T.connected h' = halfClass hG h :=
    halfClass_leaf_out hG h hr hz hl hout
  have hcut := halfClass_leaf_in hG h.symm hz hr hl hin
  have hL := order_leafCard (half hG h.symm) ⟨l,hin⟩
    (fun he => hr (congrArg Subtype.val he)) (leafHalfIn hG h.symm hr hl hin)
  change _ + 1 = order (halfClass hG h.symm) at hL
  have hh : order (halfClass T.connected h') = k := by rw [hper,hA]
  have hh' : order (halfClass T.connected h'.symm) = k := by
    change halfClass T.connected h'.symm = _ at hcut
    rw [hcut]
    have hbig := odd_other_order hG h hk hA
    omega
  have horder : Nat.card T.V = 2*k := by
    have ho := order_leafCard (arbitraryRoot G hG r) l hr hl
    change Nat.card T.V + 1 = Nat.card V at ho
    omega
  exact ⟨centroid_of_equal_halves T.connected h' (by omega) (hh'.trans hh.symm),
    centroid_of_equal_halves T.connected h'.symm (by omega) (hh.trans hh'.symm)⟩

include hk hA in
private theorem strict_centroid_of_inside_leaf {l : V} (hr : r ≠ l) (hz : z ≠ l)
    (hl : IsLeaf (arbitraryRoot G hG r) l) (hin : l ∈ cut h)
    (hsmall : ∀ x ∈ children (halfClass hG h.symm), order x < k) :
    let T := leafCard (arbitraryRoot G hG r) l hr hl
    balanced T.G (newRoot hr) 0 := by
  let T := leafCard (arbitraryRoot G hG r) l hr hl
  let h' := edgeOnCard h hr hz
  have ho : l ∉ cut h.symm := by rw [cut_symm hG h]; intro he; exact he hin
  have hper : halfClass T.connected h'.symm = halfClass hG h.symm :=
    halfClass_leaf_out hG h.symm hz hr hl ho
  have hcut := halfClass_leaf_in hG h hr hz hl hin
  have hL := order_leafCard (half hG h) ⟨l,hin⟩
    (fun he => hz (congrArg Subtype.val he)) (leafHalfIn hG h hz hl hin)
  change _ + 1 = order (halfClass hG h) at hL
  have horder : Nat.card T.V = 2*k := by
    have ho := order_leafCard (arbitraryRoot G hG r) l hr hl
    change Nat.card T.V + 1 = Nat.card V at ho
    omega
  apply balancedFromCard T.connected h' horder ?_ ?_
  · rw [hcut]
    omega
  · simpa only [hper] using hsmall

include hG h hk hA in
private theorem odd_endpoints_not_leaf (hmin : 2 ≤ k) {l : V}
    (hl : ∃! y, G.Adj l y) : r ≠ l ∧ z ≠ l := by
  have hb := odd_other_order hG h hk hA
  exact ⟨fun e => edge_end_not_leaf hG h.symm (by omega) (e.symm ▸ hl),
    fun e => edge_end_not_leaf hG h (by omega) (e.symm ▸ hl)⟩

private theorem same_pair_of_centroids {l : V} {c d : Deleted l} (hc : isCentroid (cardAt G l) c)
    (hd : isCentroid (cardAt G l) d) (he : (cardAt G l).Adj c d)
    {r' z' : Deleted l} (hr : isCentroid (cardAt G l) r') (hz : isCentroid (cardAt G l) z')
    (h' : (cardAt G l).Adj r' z') (hT : (cardAt G l).IsTree) :
    ({halfClass hT he,halfClass hT he.symm} : Multiset FiniteRootedTree.Class) =
      {halfClass hT h',halfClass hT h'.symm} := by
  by_cases hcr : c = r'
  · subst c
    have hh := centroid_other_unique hT hr hz hd h'.ne he.ne
    subst d
    rfl
  · have hcz := centroid_other_unique hT hr hz hc h'.ne (Ne.symm hcr)
    subst c
    have hdr := centroid_other_unique hT hz hr hd h'.ne' he.ne
    subst d
    exact Multiset.cons_swap _ _ _

include hk hA in
private theorem outside_pair_classify (hmin : 2 ≤ k) {l : V} {c d : Deleted l}
    (hl : IsLeaf (arbitraryRoot G hG c.val) l) (he : (cardAt G l).Adj c d)
    (hc : isCentroid (cardAt G l) c) (hd : isCentroid (cardAt G l) d) (hout : l ∉ cut h) :
    let T := leafCard (arbitraryRoot G hG c.val) l c.property hl
    ({halfClass T.connected he,halfClass T.connected he.symm} : Multiset FiniteRootedTree.Class) ∈
      CentroidPairDeck.oneSide (halfClass hG h) (trims (halfClass hG h.symm)) := by
  obtain ⟨hr,hz⟩ := odd_endpoints_not_leaf hG h hk hA hmin hl
  let T := leafCard (arbitraryRoot G hG c.val) l c.property hl
  let h' := edgeOnCard h hr hz
  have hh := both_centroids_of_outside_leaf hG h hk hA hr hz hl hout
  have hp := same_pair_of_centroids hc hd he hh.1 hh.2 h' T.connected
  have hin : l ∈ cut h.symm := by rwa [cut_symm hG h]
  have h1 := halfClass_leaf_out hG h hr hz hl hout
  have h2 := halfClass_leaf_in hG h.symm hz hr hl hin
  change ({halfClass T.connected he,halfClass T.connected he.symm} : Multiset FiniteRootedTree.Class) ∈ _
  let p : (half hG h.symm).V := ⟨l,hin⟩
  have hpn : (half hG h.symm).r ≠ p := fun eq => hr (congrArg Subtype.val eq)
  have hpl : IsLeaf (half hG h.symm) p := leafHalfIn hG h.symm hr hl hin
  let X := ofTree (leafCard (half hG h.symm) p hpn hpl)
  refine ⟨X,(trim_some_ofTree_iff _ X).mpr ⟨p,hpn,hpl,rfl⟩,?_⟩
  exact (hp.trans (congrArg₂ (fun a b => ({a,b} : Multiset FiniteRootedTree.Class)) h1 h2)).symm

include hk hA in
private theorem outside_pair_realize {m : Multiset FiniteRootedTree.Class}
    (hm : m ∈ CentroidPairDeck.oneSide (halfClass hG h) (trims (halfClass hG h.symm))) :
    m ∈ pairProfiles G hG := by
  obtain ⟨x,hx,rfl⟩ := hm
  obtain ⟨l,hr,hl,he⟩ := (trim_some_ofTree_iff (half hG h.symm) x).mp hx
  have hr' : r ≠ l.val := fun eq => hr (Subtype.ext eq)
  have hz : z ≠ l.val := fun eq => root_not_branchVerts (toward h.symm)
    (Eq.mp (congrArg (fun u => u ∈ cut h.symm) eq.symm) l.property)
  have hl' := (leaf_half_iff hG h.symm l hr'.symm).mp hl
  have hout : l.val ∉ cut h := by
    exact Eq.mp (congrArg (fun P : Set V => l.val ∈ P) (cut_symm hG h)) l.property
  have hh := both_centroids_of_outside_leaf hG h hk hA hr' hz hl' hout
  have h1 := halfClass_leaf_out hG h hr' hz hl' hout
  have h2 := (halfClass_leaf_in hG h.symm hz hr' hl' l.property).trans he
  exact ⟨l.val,newRoot hr',newRoot hz,hl',edgeOnCard h hr' hz,hh.1,hh.2,
    congrArg₂ (fun a b => ({a,b} : Multiset FiniteRootedTree.Class)) h1.symm h2.symm⟩

include hk hA in
theorem pairProfiles_odd_one (hmin : 2 ≤ k)
    (hsmall : ∀ x ∈ children (halfClass hG h.symm), order x < k) :
    pairProfiles G hG = CentroidPairDeck.oneSide (halfClass hG h) (trims (halfClass hG h.symm)) := by
  ext m
  constructor
  · rintro ⟨l,c,d,hl,hadj,hc,hd,rfl⟩
    by_cases hi : l ∈ cut h
    · obtain ⟨hr,hz⟩ := odd_endpoints_not_leaf hG h hk hA hmin hl
      have hs := strict_centroid_of_inside_leaf hG h hk hA hr hz hl hi hsmall
      have hT := (leafCard (arbitraryRoot G hG c.val) l c.property hl).connected
      exact (hadj.ne ((centroid_strict_no_other hT hs hc).symm.trans
        (centroid_strict_no_other hT hs hd))).elim
    · exact outside_pair_classify hG h hk hA hmin hl hadj hc hd hi
  · exact outside_pair_realize hG h hk hA

include hk hA in
theorem pairProfiles_odd_two {z' : V} (h' : G.Adj r z') (hA' : order (halfClass hG h') = k)
    (hsep : toward h ≠ toward h') (hmin : 2 ≤ k) :
    pairProfiles G hG =
      CentroidPairDeck.oneSide (halfClass hG h) (trims (halfClass hG h.symm)) ∪
      CentroidPairDeck.oneSide (halfClass hG h') (trims (halfClass hG h'.symm)) := by
  ext m
  constructor
  · rintro ⟨l,c,d,hl,hadj,hc,hd,rfl⟩
    by_cases hnot : l ∈ cut h
    · have hnot' : l ∉ cut h' := fun hp => Set.disjoint_left.mp (cut_disjoint h h' hsep) hnot hp
      exact Or.inr (outside_pair_classify hG h' hk hA' hmin hl hadj hc hd hnot')
    · exact Or.inl (outside_pair_classify hG h hk hA hmin hl hadj hc hd hnot)
  · rintro (hm|hm)
    · exact outside_pair_realize hG h hk hA hm
    · exact outside_pair_realize hG h' hk hA' hm

private theorem inside_leaf_profile {l : V} (hr : r ≠ l) (hz : z ≠ l)
    (hl : IsLeaf (arbitraryRoot G hG r) l) (hi : l ∈ cut h) :
    let T := leafCard (arbitraryRoot G hG r) l hr hl
    let X := ofTree (leafCard (half hG h) ⟨l,hi⟩ (fun eq => hz (congrArg Subtype.val eq))
      (leafHalfIn hG h hz hl hi))
    branchMultiset T = X ::ₘ children (halfClass hG h.symm) := by
  let T := leafCard (arbitraryRoot G hG r) l hr hl
  let h' := edgeOnCard h hr hz
  have hOut : l ∉ cut h.symm := by rw [cut_symm hG h]; exact fun x => x hi
  have h₁ := halfClass_leaf_in hG h hr hz hl hi
  have h₂ := halfClass_leaf_out hG h.symm hz hr hl hOut
  have hh := branchMultiset_split_half T.connected h'
  change branchMultiset T = halfClass T.connected h' ::ₘ children (halfClass T.connected h'.symm) at hh
  exact hh.trans (congrArg₂ (· ::ₘ ·) h₁ (congrArg children h₂))

include hk hA in
theorem centroidProfiles_odd_one (hmin : 2 ≤ k)
    (hsmall : ∀ x ∈ children (halfClass hG h.symm), order x < k) :
    centroidProfiles G hG = EvenCentroidProfile.one (halfClass hG h.symm) (halfClass hG h) := by
  ext m
  constructor
  · rintro ⟨l,c,hl,hbal,rfl⟩
    obtain ⟨hr,hz⟩ := odd_endpoints_not_leaf hG h hk hA hmin hl
    by_cases hin : l ∈ cut h
    · have hstable := strict_centroid_of_inside_leaf hG h hk hA hr hz hl hin hsmall
      have hc := balanced_unique (leafCard (arbitraryRoot G hG r) l hr hl).connected hbal hstable
      change c = newRoot hr at hc
      subst c
      exact ⟨_,(trim_some_ofTree_iff _ _).mpr ⟨⟨l,hin⟩,_,_,rfl⟩,
        (inside_leaf_profile hG h hr hz hl hin).symm⟩
    · have hcent := both_centroids_of_outside_leaf hG h hk hA hr hz hl hin
      have hT := (leafCard (arbitraryRoot G hG r) l hr hl).connected
      exact ((edgeOnCard h hr hz).ne ((centroid_strict_no_other hT hbal hcent.1).symm.trans
        (centroid_strict_no_other hT hbal hcent.2))).elim
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨l,hn,hl,he⟩ := (trim_some_ofTree_iff (half hG h) x).mp hx
    have hr : r ≠ l.val := fun eq => root_not_branchVerts (toward h)
      (Eq.mp (congrArg (fun x => x ∈ cut h) eq.symm) l.property)
    have hz : z ≠ l.val := fun eq => hn (Subtype.ext eq)
    have hl' := (leaf_half_iff hG h l hz.symm).mp hl
    have hbal := strict_centroid_of_inside_leaf hG h hk hA hr hz hl' l.property hsmall
    have hlist := inside_leaf_profile hG h hr hz hl' l.property
    exact ⟨l.val,newRoot hr,hl',hbal,hlist.trans (congrArg (· ::ₘ children (halfClass hG h.symm)) he)⟩

end OddCards

end TreeHalf

namespace RootedClass

open FiniteRootedTree Multiset

theorem trim_realized {a : Shape} {m : Multiset Shape}
    (h : m ∈ RootedBranchDeck.cards trim (children a)) :
    ∃ b ∈ trims a, children b = m := by
  refine Quotient.inductionOn a (fun T h => ?_) h
  change m ∈ RootedBranchDeck.cards trim (branchMultiset T) at h
  rw [cards_branchMultiset] at h
  obtain ⟨l,hn,hl,he⟩ := h
  exact ⟨ofTree (leafCard T l hn hl),(trim_some_ofTree_iff _ _).mpr ⟨l,hn,hl,rfl⟩,he⟩

theorem order_sum_zero {m : Multiset Shape} (h : (m.map order).sum = 0) : m = 0 := by
  by_contra hm
  obtain ⟨x,hx⟩ := Multiset.card_pos_iff_exists_mem.mp (Multiset.card_pos.mpr hm)
  have hs := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) (order x)
    (Multiset.mem_map_of_mem order hx)
  have hp := order_pos x
  omega

theorem order_sum_one {m : Multiset Shape} (h : (m.map order).sum = 1) :
    ∃ x, m = {x} ∧ order x = 1 := by
  have hn : m ≠ 0 := by rintro rfl; simp at h
  obtain ⟨x,hx⟩ := Multiset.card_pos_iff_exists_mem.mp (Multiset.card_pos.mpr hn)
  obtain ⟨r,hr⟩ := Multiset.exists_cons_of_mem hx
  rw [hr,Multiset.map_cons,Multiset.sum_cons] at h
  have hp := order_pos x
  have hr₀ : (r.map order).sum = 0 := by omega
  rw [order_sum_zero hr₀] at hr
  exact ⟨x,hr,by omega⟩

theorem children_eq_single_of_order {a b : Shape} (hb : b ∈ children a)
    (h : order a = order b + 1) : children a = {b} := by
  obtain ⟨rest,hrest⟩ := Multiset.exists_cons_of_mem hb
  have hh := order_eq_children_sum a
  rw [hrest,Multiset.map_cons,Multiset.sum_cons] at hh
  have hzero : (rest.map order).sum = 0 := by omega
  rwa [order_sum_zero hzero] at hrest

private theorem order_small_children {a b : Shape} (ho : order a = order b)
    (ha : ∀ x ∈ children a, order x = 1) (hb : ∀ x ∈ children b, order x = 1) :
    a = b := by
  have hsum (c : Shape) (hc : ∀ x ∈ children c, order x = 1) :
      (children c).card + 1 = order c := by
    have hc' : (children c).map order = Multiset.replicate (children c).card 1 := by
      rw [← Multiset.map_const']
      exact Multiset.map_congr rfl hc
    rw [order_eq_children_sum c,hc']
    simp [Nat.add_comm]
  have hk : (children a).card = (children b).card := by
    have h₁ := hsum a ha
    have h₂ := hsum b hb
    omega
  by_cases h0 : children a = 0
  · apply children_injective
    rw [h0]
    exact (Multiset.card_eq_zero.mp (by simpa [h0] using hk.symm)).symm
  obtain ⟨x,hx⟩ := Multiset.card_pos_iff_exists_mem.mp (Multiset.card_pos.mpr h0)
  have hox := ha x hx
  have ht (c : Shape) (hc : ∀ y ∈ children c, order y = 1) :
      children c = Multiset.replicate (children c).card x :=
    Multiset.eq_replicate_card.mpr (fun y hy =>
      chain_unique (chain_of_order_one (hc y hy)) (chain_of_order_one hox) ((hc y hy).trans hox.symm))
  apply children_injective
  rw [ht a ha,ht b hb,hk]

theorem singleton_child_sum_one {a x : Shape} (h : children a = {x})
    (hx : order x = 1) : order a = 2 := by
  rw [order_of_single_child h,hx]

end RootedClass

namespace OddCentroidProfile

open FiniteRootedTree RootedClass Multiset

abbrev Shape := FiniteRootedTree.Class

private theorem oneSide_varies {a b x y : Shape} {trim trim' : Set Shape}
    (h : CentroidPairDeck.oneSide a trim = CentroidPairDeck.oneSide b trim')
    (hx : x ∈ trim) (hy : y ∈ trim) (hxy : x ≠ y) : a = b := by
  by_contra hn
  have fixed {u : Shape} (hu : u ∈ trim) : b = u := by
    have hh : ({a,u} : Multiset Shape) ∈ CentroidPairDeck.oneSide b trim' := h ▸ ⟨u,hu,rfl⟩
    obtain ⟨z,hz,he⟩ := hh
    have hm : b ∈ ({a,u} : Multiset Shape) := he ▸ by simp
    simpa [Ne.symm hn] using hm
  exact hxy ((fixed hx).symm.trans (fixed hy))

private theorem recover_fixed_trim {a b d : Shape} (ha : 2 ≤ order a)
    (h : EvenCentroidProfile.one b a = EvenCentroidProfile.one d a) : b = d := by
  classical
  have hc {p q : Shape} (he : EvenCentroidProfile.one p a = EvenCentroidProfile.one q a)
      (t : Shape) : (children p).count t ≤ (children q).count t := by
    by_cases ht : t ∈ trims a
    · have hm : t ::ₘ children p ∈ EvenCentroidProfile.one q a := he ▸ ⟨t,ht,rfl⟩
      obtain ⟨w,_,hw⟩ := hm
      have hh := congrArg (Multiset.count t) hw
      change (w ::ₘ children q).count t = (t ::ₘ children p).count t at hh
      rw [Multiset.count_cons,Multiset.count_cons_self] at hh
      split at hh <;> omega
    · obtain ⟨w,hw⟩ := trims_nonempty ha
      have hm : w ::ₘ children p ∈ EvenCentroidProfile.one q a := he ▸ ⟨w,hw,rfl⟩
      obtain ⟨z,hz,hEq⟩ := hm
      have hzn : t ≠ z := fun h => ht (h.symm ▸ hz)
      have hwn : t ≠ w := fun h => ht (h.symm ▸ hw)
      have hh := congrArg (Multiset.count t) hEq
      change (z ::ₘ children q).count t = (w ::ₘ children p).count t at hh
      rw [Multiset.count_cons_of_ne hzn,Multiset.count_cons_of_ne hwn] at hh
      exact hh.ge
  apply children_injective
  ext t
  exact (hc h t).antisymm (hc h.symm t)

private theorem one_large_other_trim_shapes {b d : Shape} {k : ℕ}
    (hb : order b = k+1) (hd : d ∈ children b) (hdo : order d + 1 = k) (hk : 3 ≤ k) :
    ∃ x ∈ trims b, ∃ y ∈ trims b, x ≠ y := by
  obtain ⟨rest,hr⟩ := Multiset.exists_cons_of_mem hd
  have ht := order_eq_children_sum b
  rw [hr,Multiset.map_cons,Multiset.sum_cons] at ht
  have hrest : (rest.map order).sum = 1 := by omega
  obtain ⟨u,hu,huo⟩ := order_sum_one hrest
  rw [hu] at hr
  obtain ⟨v,hv⟩ := trims_nonempty (a := d) (by omega)
  obtain ⟨x,hx,hxc⟩ := trim_realized (a := b) (m := {d})
    ⟨u,none,{d},hr.trans (Multiset.cons_swap d u 0),huo,rfl⟩
  obtain ⟨y,hy,hyc⟩ := trim_realized (a := b) (m := v ::ₘ {u})
    ⟨d,some v,{u},hr,hv,rfl⟩
  refine ⟨x,hx,y,hy,?_⟩
  intro h
  rw [h,hyc] at hxc
  have hcr := congrArg Multiset.card hxc
  simp at hcr

/-- Two profiles distinguish the big and small sides of an odd-order tree
whose centroid has a single branch of the maximum possible size. -/
theorem recover {a b c d : Shape} {k : ℕ} (hmin : 2 ≤ k)
    (ha : order a = k) (hb : order b = k+1)
    (hc : order c = k) (hd : order d = k+1)
    (hsmall : ∀ x ∈ children b, order x < k)
    (hsmall' : ∀ x ∈ children d, order x < k)
    (hstrict : EvenCentroidProfile.one b a = EvenCentroidProfile.one d c)
    (hpairs : CentroidPairDeck.oneSide a (trims b) = CentroidPairDeck.oneSide c (trims d)) :
    a = c ∧ b = d := by
  have finish (he : b = d) : a = c ∧ b = d := by
    subst d
    exact ⟨CentroidPairDeck.oneSide_injective (trims_nonempty (by omega)) hpairs,rfl⟩
  by_cases htwo : k = 2
  · exact finish (order_small_children (hb.trans hd.symm)
      (fun x hx => by have hh := hsmall x hx; have hp := order_pos x; omega)
      (fun x hx => by have hh := hsmall' x hx; have hp := order_pos x; omega))
  by_cases hlarge : ∃ x ∈ children b, order x + 1 = k
  · obtain ⟨x,hx,hxo⟩ := hlarge
    obtain ⟨p,hp,q,hq,hpq⟩ := one_large_other_trim_shapes hb hx hxo (by omega)
    have he := oneSide_varies hpairs hp hq hpq
    subst c
    exact ⟨rfl,recover_fixed_trim (by omega) hstrict⟩
  · obtain ⟨x,hx⟩ := trims_nonempty (a := a) (by omega)
    have hl : x ::ₘ children b ∈ EvenCentroidProfile.one d c := hstrict ▸ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := hl
    have hy' : order y + 1 = k := (trim_order hy).trans hc
    have hm : y ∈ x ::ₘ children b := by rw [← he]; simp
    have hEq := (Multiset.mem_cons.mp hm).resolve_right (fun ht => hlarge ⟨y,ht,hy'⟩)
    subst y
    exact finish (children_injective ((Multiset.cons_inj_right _).mp he.symm))

end OddCentroidProfile

namespace TreeHalf

open SimpleGraph TreeCentroid TreeBranches FiniteRootedTree RootedClass ReconstructionConjecture

private theorem mem_other_children {V : Type} [Finite V] {G : SimpleGraph V} {r z : V}
    (hG : G.IsTree) (h : G.Adj r z) {x : FiniteRootedTree.Class} :
    x ∈ children (halfClass hG h.symm) ↔
      ∃ C : Branch G r, C ≠ toward h ∧ branchClass (arbitraryRoot G hG r) C = x := by
  classical
  let e := branchesAwayEquiv hG h
  change x ∈ branchMultiset (half hG h.symm) ↔ _
  constructor
  · intro hx
    unfold branchMultiset at hx
    obtain ⟨C,_,hC⟩ := Multiset.mem_map.mp hx
    exact ⟨(e C).val,(e C).property,(branchAway_class hG h C).symm.trans hC⟩
  · rintro ⟨C,hneq,hC⟩
    let C' := e.symm ⟨C,hneq⟩
    have he : (branchesAwayEquiv hG h C').val = C :=
      congrArg Subtype.val (e.apply_symm_apply ⟨C,hneq⟩)
    have hx := (branchAway_class hG h C').trans
      ((congrArg (branchClass (arbitraryRoot G hG r)) he).trans hC)
    exact hx ▸ branchList_single_le (T := half hG h.symm) (C := C')

private theorem half_size_at_branch {V : Type} [Finite V] {G : SimpleGraph V} {r : V}
    (hG : G.IsTree) (C : Branch G r) :
    order (halfClass hG (adj_attachment hG C)) = Nat.card C.supp := by
  rw [halfClass_eq_branch,toward_attachment]
  rfl

private theorem children_of_two_large {V : Type} [Finite V] {G : SimpleGraph V} {r z z' : V}
    (hG : G.IsTree) (h : G.Adj r z) (h' : G.Adj r z') (hne : toward h' ≠ toward h)
    (hord : order (halfClass hG h.symm) = order (halfClass hG h') + 1) :
    children (halfClass hG h.symm) = {halfClass hG h'} := by
  apply children_eq_single_of_order ?_ hord
  exact (mem_other_children hG h).mpr ⟨toward h',hne,(halfClass_eq_branch hG h').symm⟩

private theorem path_at_three {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (hV : 3 ≤ Fintype.card V) (hcard : Nat.card V = 3)
    (hG : G.IsTree) (h : Hypomorphic G H) : Nonempty (G ≃g H) := by
  apply TreeReconstruction.path_reconstruction hV hG ?_ h
  classical
  intro x
  have hF : Fintype.card V = 3 := by simpa only [Nat.card_eq_fintype_card] using hcard
  rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
  have hd := G.degree_lt_card_verts x
  omega

/-- Reconstruction for all odd-order trees. -/
theorem reconstruct_odd {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (hV : 3 ≤ Fintype.card V) (hG : G.IsTree)
    (h : Hypomorphic G H) (hodd : Odd (Nat.card V)) : Nonempty (G ≃g H) := by
  classical
  obtain ⟨k,hk⟩ := hodd
  have hn : Nat.card V = 2*k+1 := by omega
  have hV' : 3 ≤ Nat.card V := by simpa only [Nat.card_eq_fintype_card] using hV
  by_cases hk₂ : 2 ≤ k
  swap
  · exact path_at_three hV (by omega) hG h
  obtain ⟨r,hr⟩ := exists_centroid hG
  by_cases hbal : balanced G r 1
  · exact reconstruct_balanced hV hG h r hbal
  have hlarge : ∃ C : Branch G r, Nat.card C.supp = k := by
    unfold balanced at hbal
    push Not at hbal
    obtain ⟨C,hsize⟩ := hbal
    have hcent := hr C
    exact ⟨C,by omega⟩
  obtain ⟨C,hC⟩ := hlarge
  have hH := TreeReconstruction.tree_of_hypomorphic hV hG h
  have hn' : Nat.card W = 2*k+1 := by simpa only [Nat.card_eq_fintype_card,h.card_eq] using hn
  have hp := pairProfiles_hypomorphic hV hG h hH
  have hspect := centroidProfiles_hypomorphic hV hG h hH
  obtain ⟨σ,hσ⟩ := h
  let e := (hσ r).some
  let F := e.connectedComponentEquiv
  have hSize (X : Branch G r) : Nat.card (F X).supp = Nat.card X.supp :=
    (Nat.card_congr (X.isoEquivSupp e)).symm
  let hG₁ := adj_attachment hG C
  let hH₁ := adj_attachment hH (F C)
  have hgA : order (halfClass hG hG₁) = k := (half_size_at_branch hG C).trans hC
  have hhA : order (halfClass hH hH₁) = k :=
    (half_size_at_branch hH (F C)).trans ((hSize C).trans hC)
  by_cases hsecond : ∃ B : Branch G r, B ≠ C ∧ Nat.card B.supp = k
  · obtain ⟨B,hBC,hB⟩ := hsecond
    let hG₂ := adj_attachment hG B
    let hH₂ := adj_attachment hH (F B)
    have hgB : order (halfClass hG hG₂) = k := (half_size_at_branch hG B).trans hB
    have hhB : order (halfClass hH hH₂) = k :=
      (half_size_at_branch hH (F B)).trans ((hSize B).trans hB)
    have neqG : toward hG₁ ≠ toward hG₂ := by
      change toward (adj_attachment hG C) ≠ toward (adj_attachment hG B)
      simpa only [toward_attachment] using hBC.symm
    have neqH : toward hH₁ ≠ toward hH₂ := by
      change toward (adj_attachment hH (F C)) ≠ toward (adj_attachment hH (F B))
      simpa only [toward_attachment] using F.injective.ne hBC.symm
    have hG'₁ : children (halfClass hG hG₁.symm) = {halfClass hG hG₂} :=
      children_of_two_large hG hG₁ hG₂ neqG.symm ((odd_other_order hG hG₁ hn hgA).trans (by rw [hgB]))
    have hG'₂ : children (halfClass hG hG₂.symm) = {halfClass hG hG₁} :=
      children_of_two_large hG hG₂ hG₁ neqG ((odd_other_order hG hG₂ hn hgB).trans (by rw [hgA]))
    have hH'₁ : children (halfClass hH hH₁.symm) = {halfClass hH hH₂} :=
      children_of_two_large hH hH₁ hH₂ neqH.symm ((odd_other_order hH hH₁ hn' hhA).trans (by rw [hhB]))
    have hH'₂ : children (halfClass hH hH₂.symm) = {halfClass hH hH₁} :=
      children_of_two_large hH hH₂ hH₁ neqH ((odd_other_order hH hH₂ hn' hhB).trans (by rw [hhA]))
    rw [pairProfiles_odd_two hG hG₁ hn hgA hG₂ hgB neqG hk₂,
      pairProfiles_odd_two hH hH₁ hn' hhA hH₂ hhB neqH hk₂,
      trims_eq_unaryTrims hG'₁,trims_eq_unaryTrims hG'₂,
      trims_eq_unaryTrims hH'₁,trims_eq_unaryTrims hH'₂] at hp
    have hh := recover_unary_pairs (hgA.trans hgB.symm) (hgA.trans hhA.symm)
      (hgA.trans hhB.symm) (unaryTrims_nonempty hG'₂) (unaryTrims_nonempty hG'₁)
      (unaryTrims_nonempty hH'₂) (unaryTrims_nonempty hH'₁) hp
    rcases hh with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
    · exact assemble hG hH hG₁ hH₁ h₁ (children_injective (hG'₁.trans (by simpa [h₂] using hH'₁.symm)))
    · exact assemble hG hH hG₁ hH₂ h₁ (children_injective (hG'₁.trans (by simpa [h₂] using hH'₂.symm)))
  · have hsmall (B : Branch G r) (hB : B ≠ C) : Nat.card B.supp < k := by
      have hb := hr B
      by_contra! hbn
      exact hsecond ⟨B,hB,by omega⟩
    have smallG : ∀ x ∈ children (halfClass hG hG₁.symm), order x < k := by
      intro x hx
      obtain ⟨B,hB,rfl⟩ := (mem_other_children hG hG₁).mp hx
      apply hsmall B
      change B ≠ toward (adj_attachment hG C) at hB
      rwa [toward_attachment] at hB
    have smallH : ∀ x ∈ children (halfClass hH hH₁.symm), order x < k := by
      intro x hx
      obtain ⟨B,hB,rfl⟩ := (mem_other_children hH hH₁).mp hx
      change B ≠ toward (adj_attachment hH (F C)) at hB
      rw [toward_attachment] at hB
      obtain ⟨B',rfl⟩ := F.surjective B
      change Nat.card (F B').supp < k
      rw [hSize B']
      exact hsmall B' (fun he => hB (congrArg F he))
    rw [pairProfiles_odd_one hG hG₁ hn hgA hk₂ smallG,
      pairProfiles_odd_one hH hH₁ hn' hhA hk₂ smallH] at hp
    rw [centroidProfiles_odd_one hG hG₁ hn hgA hk₂ smallG,
      centroidProfiles_odd_one hH hH₁ hn' hhA hk₂ smallH] at hspect
    have he := OddCentroidProfile.recover hk₂ hgA (odd_other_order hG hG₁ hn hgA)
      hhA (odd_other_order hH hH₁ hn' hhA) smallG smallH hspect hp
    exact assemble hG hH hG₁ hH₁ he.1 he.2

end TreeHalf

theorem OMA.solution :
    type_of% @ReconstructionConjecture.reconstruction_conjecture.variants.tree := by
  intro V W _ _ hV G H hc ha h
  rcases Nat.even_or_odd (Nat.card V) with he|ho
  · exact TreeHalf.reconstruct_even hV ⟨hc,ha⟩ h he
  · exact TreeHalf.reconstruct_odd hV ⟨hc,ha⟩ h ho