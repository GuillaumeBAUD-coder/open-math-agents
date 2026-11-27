import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1

/-!
# Small center components in the reconstruction of a tree

A diameter path supplies two pendant arms of full radius. After deleting a
leaf, the center is the unique vertex of degree at least three within the
radius bound of every remaining vertex. Comparing the two outer levels in
the leaf cards identifies corresponding arm tips. Their shortened arms can
be exchanged by a card automorphism before the deleted tips are restored.

Credit: @Deldor14. The tree deletion and distance lemmas are adapted from
@green-notes' proof of the preceding step.
-/
namespace OMA
namespace TreeArms
open SimpleGraph
open Classical
variable {V : Type*} {G : SimpleGraph V} {c : V} {n : Nat}

structure Arm (G : SimpleGraph V) (c : V) (n : Nat) where
  vertex : Fin n ↪ V
  away : ∀ i, vertex i ≠ c
  internal : ∀ i j, G.Adj (vertex i) (vertex j) ↔ i.val+1=j.val ∨ j.val+1=i.val
  external : ∀ i x, x ∉ Set.range vertex →
    (G.Adj (vertex i) x ↔ i.val=0 ∧ x=c)

-- Tree deletion and distance lemmas adapted from @green-notes, tree.R1.H3.R1.H2.
private lemma isTree_dist_eq_length_of_isPath {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    {x y : U} (p : T.Walk x y) (hp : p.IsPath) :
    p.length = T.dist x y := by
  obtain ⟨q, hq, hqlen⟩ := hT.connected.exists_path_of_dist x y
  have hsub : (⟨p, hp⟩ : T.Path x y) = ⟨q, hq⟩ := (hT.isAcyclic.subsingleton_path x y).elim _ _
  have hpq : p = q := congrArg Subtype.val hsub
  rw [hpq, hqlen]

private lemma ncard_neighborSet_eq_degree {U : Type} [Fintype U] (T : SimpleGraph U) (u : U) :
    (T.neighborSet u).ncard = T.degree u := by
  rw [← T.card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card' (T.neighborSet u)]
  simp [Set.toFinset_card]

private lemma iso_edist_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) (a₁ a₂ : A) : GB.edist (φ a₁) (φ a₂) = GA.edist a₁ a₂ := by
  apply le_antisymm
  · dsimp only [SimpleGraph.edist]
    rw [le_iInf_iff]
    intro w
    exact (SimpleGraph.edist_le (w.map φ.toHom)).trans (by simp)
  · dsimp only [SimpleGraph.edist]
    rw [le_iInf_iff]
    intro w
    exact (SimpleGraph.edist_le ((w.map φ.symm.toHom).copy (φ.symm_apply_apply a₁) (φ.symm_apply_apply a₂))).trans
      (by rw [Nat.cast_le, Walk.length_copy, Walk.length_map])

private lemma degree_induce_compl_singleton_of_adj {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) (hadj : T.Adj a v) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ + 1 = T.degree a := by
  let f : ({v}ᶜ : Set U) ↪ U := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap_not : v ∉ ((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f := by
    intro h
    rw [Finset.mem_map] at h
    obtain ⟨x, _, hxv⟩ := h
    exact x.2 hxv
  have heq : insert v (((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f) = T.neighborFinset a := by
    ext y
    rw [Finset.mem_insert, Finset.mem_map, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro (rfl | ⟨x, hx, rfl⟩)
      · exact hadj
      · rw [SimpleGraph.mem_neighborFinset] at hx
        exact hx
    · intro hay
      by_cases hyv : y = v
      · exact Or.inl hyv
      · refine Or.inr ⟨⟨y, hyv⟩, ?_, rfl⟩
        rw [SimpleGraph.mem_neighborFinset]
        exact hay
  have hcard := congrArg Finset.card heq
  rw [Finset.card_insert_of_notMem hmap_not, Finset.card_map,
    (T.induce {v}ᶜ).card_neighborFinset_eq_degree, T.card_neighborFinset_eq_degree] at hcard
  omega

private lemma degree_induce_compl_singleton_of_not_adj {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) (hnadj : ¬ T.Adj a v) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ = T.degree a := by
  let f : ({v}ᶜ : Set U) ↪ U := ⟨Subtype.val, Subtype.val_injective⟩
  have heq : ((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f = T.neighborFinset a := by
    ext y
    rw [Finset.mem_map, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [SimpleGraph.mem_neighborFinset] at hx
      exact hx
    · intro hay
      have hyv : y ≠ v := fun h => hnadj (h ▸ hay)
      refine ⟨⟨y, hyv⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact hay
  have hcard := congrArg Finset.card heq
  rw [Finset.card_map, (T.induce {v}ᶜ).card_neighborFinset_eq_degree,
    T.card_neighborFinset_eq_degree] at hcard
  exact hcard

private lemma degree_induce_compl_le {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ ≤ T.degree a := by
  by_cases hadj : T.Adj a v
  · have := degree_induce_compl_singleton_of_adj T hav hadj
    omega
  · rw [degree_induce_compl_singleton_of_not_adj T hav hadj]

private lemma induce_compl_singleton_isTree_of_deg_one {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hdeg1 : T.degree v = 1) :
    (T.induce {v}ᶜ).IsTree :=
  ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hdeg1, hT.isAcyclic.induce {v}ᶜ⟩

private lemma induce_compl_singleton_dist_eq {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hT' : (T.induce {v}ᶜ).IsTree)
    (a b : ({v}ᶜ : Set U)) :
    (T.induce {v}ᶜ).dist a b = T.dist a.1 b.1 := by
  obtain ⟨p, hp, hplen⟩ := hT'.connected.exists_path_of_dist a b
  let g : T.induce {v}ᶜ →g T := (SimpleGraph.Embedding.induce ({v}ᶜ : Set U)).toHom
  have hmap : (p.map g).IsPath := hp.map Subtype.val_injective
  have hdist := isTree_dist_eq_length_of_isPath T hT (p.map g) hmap
  rw [Walk.length_map, hplen] at hdist
  exact hdist


private lemma shortest_induced {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (short : p.length = G.dist u v) :
    G.isInducedPath p.support := by
  refine ⟨(p.isPath_of_length_eq_dist short).support_nodup,?_⟩
  intro i j
  have bi : i.val ≤ p.length := by have h := i.isLt; have := p.length_support; omega
  have bj : j.val ≤ p.length := by have h := j.isLt; have := p.length_support; omega
  change G.Adj p.support[i.val] p.support[j.val] ↔ _
  rw [p.support_getElem_eq_getVert i.isLt,p.support_getElem_eq_getVert j.isLt]
  have near {a b : ℕ} (ha : a ≤ p.length) (hb : b ≤ p.length)
      (ad : G.Adj (p.getVert a) (p.getVert b)) : b ≤ a+1 := by
    have d := G.dist_le ((p.take a).append ((p.drop b).cons ad))
    rw [← short,Walk.length_append,Walk.length_cons,Walk.take_length,Walk.drop_length] at d
    omega
  constructor
  · intro h
    have ij : i.val ≠ j.val := fun eq => h.ne (congrArg p.getVert eq)
    have := near bi bj h
    have := near bj bi h.symm
    omega
  · rintro (e|e)
    · rw [← e]
      exact p.adj_getVert_succ (by omega)
    · rw [← e]
      exact (p.adj_getVert_succ (by omega)).symm


private theorem swap_arms (a b : Arm G c n)
    (apart : ∀ i j, a.vertex i ≠ b.vertex j) :
    ∃ e : G ≃g G, e c = c ∧ (∀ i, e (a.vertex i) = b.vertex i) := by
  classical
  let swap (x : V) := if h : x ∈ Set.range a.vertex then b.vertex h.choose
    else if k : x ∈ Set.range b.vertex then a.vertex k.choose else x
  have ab (i) : a.vertex i ∉ Set.range b.vertex := fun ⟨j,e⟩ => apart i j e.symm
  have ba (i) : b.vertex i ∉ Set.range a.vertex := fun ⟨j,e⟩ => apart j i e
  have left (i) : swap (a.vertex i) = b.vertex i := by
    let h : a.vertex i ∈ Set.range a.vertex := ⟨i,rfl⟩
    simp only [swap,dif_pos h]
    exact congrArg b.vertex (a.vertex.injective h.choose_spec)
  have right (i) : swap (b.vertex i) = a.vertex i := by
    let k : b.vertex i ∈ Set.range b.vertex := ⟨i,rfl⟩
    simp only [swap,dif_neg (ba i),dif_pos k]
    exact congrArg a.vertex (b.vertex.injective k.choose_spec)
  have fixed {x} (hx : x ∉ Set.range a.vertex) (hy : x ∉ Set.range b.vertex) : swap x = x := by
    simp only [swap,dif_neg hx,dif_neg hy]
  have cases (x : V) : (∃ i, a.vertex i = x) ∨ (∃ i, b.vertex i = x) ∨
      (x ∉ Set.range a.vertex ∧ x ∉ Set.range b.vertex) := by
    by_cases h : x ∈ Set.range a.vertex
    · exact Or.inl h
    · by_cases k : x ∈ Set.range b.vertex
      · exact Or.inr (Or.inl k)
      · exact Or.inr (Or.inr ⟨h,k⟩)
  have undo (x : V) : swap (swap x) = x := by
    rcases cases x with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨ha,hb⟩
    · rw [left,right]
    · rw [right,left]
    · rw [fixed ha hb,fixed ha hb]
  have cross (i j) : ¬ G.Adj (a.vertex i) (b.vertex j) := by
    intro h
    exact b.away j ((a.external i _ (ba j)).mp h).2
  have respects (x y) : G.Adj (swap x) (swap y) ↔ G.Adj x y := by
    rcases cases x with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨xa,xb⟩ <;>
      rcases cases y with ⟨j,rfl⟩ | ⟨j,rfl⟩ | ⟨ya,yb⟩
    · rw [left,left,a.internal,b.internal]
    · rw [left,right]; exact iff_of_false (fun h => cross j i h.symm) (cross i j)
    · rw [left,fixed ya yb,a.external i y ya,b.external i y yb]
    · rw [right,left]; exact iff_of_false (cross i j) (fun h => cross j i h.symm)
    · rw [right,right,a.internal,b.internal]
    · rw [right,fixed ya yb,a.external i y ya,b.external i y yb]
    · rw [fixed xa xb,left,G.adj_comm x (b.vertex j),G.adj_comm x (a.vertex j),
        a.external j x xa,b.external j x xb]
    · rw [fixed xa xb,right,G.adj_comm x (a.vertex j),G.adj_comm x (b.vertex j),
        a.external j x xa,b.external j x xb]
    · rw [fixed xa xb,fixed ya yb]
  have ac : c ∉ Set.range a.vertex := fun ⟨i,h⟩ => a.away i h
  have bc : c ∉ Set.range b.vertex := fun ⟨i,h⟩ => b.away i h
  let e : G ≃g G :=
    {toFun := swap
     invFun := swap
     left_inv := undo
     right_inv := undo
     map_rel_iff' := fun {x y} => respects x y}
  exact ⟨e,fixed ac bc,left⟩

private lemma Arm.degree_bound [Fintype V] (a : Arm G c n) (i : Fin n) :
    (G.neighborSet (a.vertex i)).ncard ≤ 2 := by
  classical
  let prev := if hi : 0 < i.val then a.vertex ⟨i.val-1,by omega⟩ else c
  let next := if hi : i.val+1 < n then a.vertex ⟨i.val+1,hi⟩ else c
  have sub : G.neighborSet (a.vertex i) ⊆ ({prev,next} : Set V) := by
    intro x hx
    change G.Adj (a.vertex i) x at hx
    by_cases h : x ∈ Set.range a.vertex
    · obtain ⟨j,rfl⟩ := h
      rcases (a.internal i j).mp hx with ij|ji
      · have hi : i.val+1 < n := by omega
        right
        simp only [Set.mem_singleton_iff,next,dif_pos hi]
        exact congrArg a.vertex (Fin.ext ij.symm)
      · have hi : 0 < i.val := by omega
        left
        simp only [prev,dif_pos hi]
        exact congrArg a.vertex (Fin.ext (by change j.val = i.val-1; omega))
    · obtain ⟨zero,rfl⟩ := (a.external i x h).mp hx
      left
      simp [prev,zero]
  apply (Set.ncard_le_ncard sub).trans
  by_cases h : prev=next
  · simp [h]
  · exact (Set.ncard_pair h).le

private lemma Arm.tip_only (a : Arm G c (n+2)) (x : V) :
    G.Adj (a.vertex (Fin.last (n+1))) x ↔ x = a.vertex (Fin.last n).castSucc := by
  constructor
  · intro ad
    by_cases h : x ∈ Set.range a.vertex
    · obtain ⟨j,rfl⟩ := h
      have := (a.internal _ j).mp ad
      apply congrArg a.vertex
      apply Fin.ext
      simp only [Fin.val_last,Fin.val_castSucc] at *
      omega
    · have := ((a.external _ x h).mp ad).1
      simp at this
  · rintro rfl
    exact (a.internal _ _).mpr (Or.inr rfl)

private def Arm.map {W : Type*} {H : SimpleGraph W} (a : Arm G c n) (f : G ≃g H) :
    Arm H (f c) n where
  vertex := a.vertex.trans f.toEquiv.toEmbedding
  away i := fun h => a.away i (f.injective h)
  internal i j := f.map_adj_iff.trans (a.internal i j)
  external i y hy := by
    have pre : f.symm y ∉ Set.range a.vertex := by
      rintro ⟨j,h⟩
      exact hy ⟨j,by simp [h]⟩
    have eq : G.Adj (a.vertex i) (f.symm y) ↔ H.Adj (f (a.vertex i)) y := by
      rw [← f.map_adj_iff]; simp
    change H.Adj (f (a.vertex i)) y ↔ _
    rw [← eq,a.external i _ pre]
    exact and_congr_right fun _ => f.toEquiv.symm_apply_eq

private def Arm.shorten (a : Arm G c (n+1)) :
    Arm (G.induce {a.vertex (Fin.last n)}ᶜ)
      (⟨c,(a.away (Fin.last n)).symm⟩ : ({a.vertex (Fin.last n)}ᶜ : Set V)) n where
  vertex := ⟨fun i => ⟨a.vertex i.castSucc,fun h => Fin.castSucc_ne_last i (a.vertex.injective h)⟩,
    fun _ _ h => Fin.castSucc_injective _ (a.vertex.injective (congrArg Subtype.val h))⟩
  away i := fun h => a.away i.castSucc (congrArg Subtype.val h)
  internal i j := a.internal i.castSucc j.castSucc
  external i y hy := by
    have pre : y.val ∉ Set.range a.vertex := by
      rintro ⟨j,h⟩
      refine Fin.lastCases (motive := fun j => a.vertex j = y.val → False) ?_ ?_ j h
      · exact fun e => y.property e.symm
      · intro k e
        exact hy ⟨k,Subtype.ext e⟩
    change G.Adj (a.vertex i.castSucc) y.val ↔ _
    rw [a.external _ _ pre]
    simp [Subtype.ext_iff]

private theorem Arm.cross {x z : V} (a : Arm G c n)
    (hx : x ∈ Set.range a.vertex) (hz : z ∉ Set.range a.vertex)
    (p : G.Walk x z) : c ∈ p.support := by
  induction p with
  | nil => exact (hz hx).elim
  | @cons u v w h q ih =>
    by_cases vmem : v ∈ Set.range a.vertex
    · exact List.mem_cons_of_mem _ (ih vmem hz)
    · obtain ⟨i,rfl⟩ := hx
      have e := ((a.external i v vmem).mp h).2
      exact List.mem_cons_of_mem _ (e ▸ q.start_mem_support)

private theorem Arm.dist_outside [Fintype V] (a : Arm G c n) (conn : G.Connected)
    {x y : V} (hx : x ∈ Set.range a.vertex) (hy : y ∉ Set.range a.vertex) :
    G.dist x y = G.dist x c + G.dist c y := by
  classical
  obtain ⟨p,_,len⟩ := conn.exists_path_of_dist x y
  have hc := a.cross hx hy p
  let l := p.takeUntil c hc
  let r := p.dropUntil c hc
  have le := G.dist_le l
  have re := G.dist_le r
  have sz := congrArg Walk.length (p.take_spec hc)
  rw [Walk.length_append] at sz
  change l.length + r.length = p.length at sz
  have tr := (conn x c).dist_triangle_left y
  omega

private lemma Arm.internalNear (a : Arm G c n) (i j : Fin n) :
    G.dist (a.vertex i) (a.vertex j) < n := by
  classical
  let f : pathGraph n →g G :=
    { toFun := a.vertex
      map_rel' := fun {i j} h => (a.internal i j).mpr (pathGraph_adj.mp h) }
  obtain ⟨p,hp,_⟩ := ((pathGraph_preconnected n) i j).exists_path_of_dist
  have l := G.dist_le (p.map f)
  simp only [Walk.length_map] at l
  have q := hp.length_lt
  simp only [Fintype.card_fin] at q
  exact lt_of_le_of_lt l q

private lemma arms_disjoint_of_far (a b : Arm G c n) (conn : G.Connected) {i j : Fin n}
    (far : 2*n ≤ G.dist (a.vertex i) (b.vertex j)) :
    ∀ p q, a.vertex p ≠ b.vertex q := by
  intro p q e
  have l := a.internalNear i p
  have k := b.internalNear q j
  have tr := (conn (a.vertex i) (a.vertex p)).dist_triangle_left (b.vertex j)
  rw [e] at l tr
  omega

private lemma degree_center [Fintype V] (conn : G.Connected) (a b : Arm G c (n+1))
    (apart : ∀ i j, a.vertex i ≠ b.vertex j)
    (branch : ∃ u : V, 3 ≤ (G.neighborSet u).ncard) :
    3 ≤ (G.neighborSet c).ncard := by
  classical
  by_contra! d
  have edge (a : Arm G c (n+1)) : G.Adj c (a.vertex 0) := by
    have only := a.external 0 c (fun ⟨j,h⟩ => a.away j h)
    exact (only.mpr ⟨rfl,rfl⟩).symm
  have first {y} (h : G.Adj c y) : y=a.vertex 0 ∨ y=b.vertex 0 := by
    by_contra! ne
    exact (Nat.not_lt_of_ge (show (G.neighborSet c).ncard ≤ 2 by omega))
      ((Set.two_lt_ncard_iff (Set.toFinite _)).mpr ⟨a.vertex 0,b.vertex 0,y,edge a,edge b,h,
        apart 0 0,ne.1.symm,ne.2.symm⟩)
  let S (u : V) : Prop := u=c ∨ u∈Set.range a.vertex ∨ u∈Set.range b.vertex
  have closed {x y} (hx : S x) (ad : G.Adj x y) : S y := by
    rcases hx with rfl | ⟨i,rfl⟩ | ⟨j,rfl⟩
    · rcases first ad with rfl|rfl
      · exact Or.inr (Or.inl ⟨0,rfl⟩)
      · exact Or.inr (Or.inr ⟨0,rfl⟩)
    · by_cases h : y∈Set.range a.vertex
      · exact Or.inr (Or.inl h)
      · exact Or.inl ((a.external _ _ h).mp ad).2
    · by_cases h : y∈Set.range b.vertex
      · exact Or.inr (Or.inr h)
      · exact Or.inl ((b.external _ _ h).mp ad).2
  have propagate {u v} (p : G.Walk u v) (h : S u) : S v := by
    induction p with
    | nil => exact h
    | cons ad p ih => exact ih (closed h ad)
  obtain ⟨u,hu⟩ := branch
  rcases propagate (conn c u).some (Or.inl rfl) with rfl|⟨i,rfl⟩|⟨j,rfl⟩
  · omega
  · have := a.degree_bound i; omega
  · have := b.degree_bound j; omega

private lemma arm_from_component {V : Type*} [Fintype V] (G : SimpleGraph V) (c : V)
    {n : Nat} (hn : 0<n) (f : Fin (n+1) ↪ V) (start : f 0 = c)
    (induced : ∀ i j, G.Adj (f i) (f j) ↔ i.val+1=j.val ∨ j.val+1=i.val)
    (small : ∀ C : (G.induce {c}ᶜ).ConnectedComponent, C.supp.ncard ≤ n) :
    ∃ a : Arm G c n, ∀ i, a.vertex i = f i.succ := by
  classical
  have away (i : Fin n) : f i.succ ≠ c := by
    rw [← start]; exact fun h => Fin.succ_ne_zero _ (f.injective h)
  let g (i : Fin n) : ({c}ᶜ : Set V) := ⟨f i.succ,away i⟩
  let u : Fin n := ⟨0,hn⟩
  let graph := G.induce {c}ᶜ
  let hom : pathGraph n →g graph :=
    { toFun := g
      map_rel' := fun {i j} h => (induced i.succ j.succ).mpr (by
        have := pathGraph_adj.mp h
        simp only [Fin.val_succ]
        omega) }
  let C := graph.connectedComponentMk (g u)
  have mem (i : Fin n) : g i ∈ C.supp :=
    ConnectedComponent.sound (((pathGraph_preconnected n) i u).map hom)
  let emb (i : Fin n) : C.supp := ⟨g i,mem i⟩
  have inj : Function.Injective emb := by
    intro i j e
    exact Fin.succ_injective n (f.injective (congrArg (fun z : C.supp => z.1.1) e))
  have box : Fintype.card C.supp ≤ n := by rw [Set.fintypeCard_eq_ncard]; exact small C
  have counter := Fintype.card_le_of_injective emb inj
  have onto : Function.Surjective emb :=
    ((Fintype.bijective_iff_injective_and_card emb).mpr ⟨inj,by simpa using le_antisymm counter (by simpa using box)⟩).2
  let tail : Fin n ↪ V := ⟨fun i => f i.succ,fun _ _ h => Fin.succ_injective n (f.injective h)⟩
  refine ⟨⟨tail,away,?_,?_⟩,fun _ => rfl⟩
  · intro i j
    change G.Adj (f i.succ) (f j.succ) ↔ _
    rw [induced]
    simp only [Fin.val_succ]
    omega
  · intro i y out
    by_cases eq : y=c
    · subst y
      change G.Adj (f i.succ) c ↔ _
      rw [← start,induced]
      simp [Fin.val_succ]
    · suffices ¬ G.Adj (tail i) y by simp [this,eq]
      intro ad
      let z : ({c}ᶜ : Set V) := ⟨y,eq⟩
      have adj : graph.Adj (g i) z := ad
      have zz := (C.mem_supp_congr_adj adj).mp (mem i)
      obtain ⟨j,hj⟩ := onto ⟨z,zz⟩
      exact out ⟨j,congrArg (fun z : C.supp => z.1.1) hj⟩

private lemma max_arm {V : Type*} [Fintype V] (G : SimpleGraph V) (conn : G.Connected)
    (c x : V) (k : ℕ) (hx : G.dist c x = k+1)
    (small : ∀ C : (G.induce {c}ᶜ).ConnectedComponent, C.supp.ncard ≤ k+1) :
    ∃ a : Arm G c (k+1), a.vertex (Fin.last k) = x := by
  classical
  obtain ⟨p,path,hlen⟩ := conn.exists_path_of_dist c x
  have len : p.length = k+1 := hlen.trans hx
  let f : Fin (k+1+1) ↪ V :=
    ⟨fun i => p.getVert i.val,fun i j h => Fin.ext (path.getVert_injOn (show i.val ≤ p.length by omega) (show j.val ≤ p.length by omega) h)⟩
  have ad (i j : Fin (k+1+1)) :
      G.Adj (f i) (f j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
    let cv (i : Fin (k+1+1)) : Fin p.support.length :=
      ⟨i.val,by rw [p.length_support,len];exact i.isLt⟩
    have eq (i : Fin (k+1+1)) : p.support.get (cv i) = f i :=
      p.support_getElem_eq_getVert (cv i).isLt
    simpa only [eq,cv] using (shortest_induced p hlen).2 (cv i) (cv j)
  obtain ⟨a,ha⟩ := arm_from_component G c (by omega) f (by change p.getVert 0 = c; exact p.getVert_zero) ad small
  refine ⟨a,?_⟩
  rw [ha]
  change p.getVert (k+1) = x
  rw [←len,p.getVert_length]

private lemma hub_and_tips {V : Type} [Fintype V] (G : SimpleGraph V) (tree : G.IsTree)
    (c : V) (k : Nat) (hd : G.diam = 2*(k+2)) (he : G.eccent c = k+2)
    (small : ∀ C : (G.induce {c}ᶜ).ConnectedComponent, C.supp.ncard ≤ k+2)
    (br : ∃ x, 3 ≤ (G.neighborSet x).ncard) :
    3 ≤ G.degree c ∧ (∀ x, G.dist c x ≤ k+2) ∧
      ∀ v, ∃ a : Arm G c (k+2), a.vertex (Fin.last (k+1)) ≠ v ∧
        G.dist c (a.vertex (Fin.last (k+1))) = k+2 := by
  classical
  have : Nonempty V := tree.connected.nonempty
  have upper (x : V) : G.dist c x ≤ k+2 := by
    apply (Nat.cast_le (α := ℕ∞)).mp
    rw [(tree.connected c x).coe_dist_eq_edist]
    have h := @edist_le_eccent _ G c x
    simpa [he] using h
  obtain ⟨u,w,e⟩ := G.exists_dist_eq_diam
  have far := e.trans hd
  have tr := (tree.connected u c).dist_triangle_left w
  rw [(G.dist_comm (u:=u) (v:=c))] at tr
  have uc : G.dist c u = k+2 := by have := upper u; have := upper w; omega
  have wc : G.dist c w = k+2 := by have := upper w; omega
  obtain ⟨a,au⟩ := max_arm G tree.connected c u (k+1) uc small
  obtain ⟨b,bw⟩ := max_arm G tree.connected c w (k+1) wc small
  have far' : 2*(k+2) ≤ G.dist (a.vertex (Fin.last (k+1))) (b.vertex (Fin.last (k+1))) := by
    rw [au,bw,far]
  have dg := degree_center tree.connected a b (arms_disjoint_of_far a b tree.connected far') br
  rw [ncard_neighborSet_eq_degree] at dg
  refine ⟨dg,upper,?_⟩
  intro v
  by_cases eq : u=v
  · refine ⟨b,?_,by rwa [bw]⟩
    rw [bw,←eq]
    intro h
    rw [h,G.dist_self] at far
    omega
  · exact ⟨a,by rwa [au],by rwa [au]⟩

private lemma hub_card {V : Type} [Fintype V] (G : SimpleGraph V) (tree : G.IsTree)
    (c v : V) (k : Nat) (dc : 3 ≤ G.degree c) (dv : G.degree v = 1)
    (noLeaf : ∀ x, G.Adj c x → 2 ≤ (G.neighborSet x).ncard)
    (upper : ∀ x, G.dist c x ≤ k+2)
    (surv : ∃ a : Arm G c (k+2), a.vertex (Fin.last (k+1)) ≠ v ∧
        G.dist c (a.vertex (Fin.last (k+1))) = k+2) :
    ∀ z : ({v}ᶜ : Set V), (3 ≤ (G.induce {v}ᶜ).degree z ∧
      ∀ x, (G.induce {v}ᶜ).dist z x ≤ k+2) ↔ z.val=c := by
  classical
  have cardTree := induce_compl_singleton_isTree_of_deg_one G tree dv
  have distances := induce_compl_singleton_dist_eq G tree cardTree
  intro z
  constructor
  · rintro ⟨branch,ecc⟩
    obtain ⟨a,ne,dist⟩ := surv
    let tip := a.vertex (Fin.last (k+1))
    have high : 3 ≤ G.degree z.val := branch.trans (degree_induce_compl_le G z.property)
    have notIn : z.val ∉ Set.range a.vertex := by
      rintro ⟨i,eq⟩
      have b := a.degree_bound i
      rw [ncard_neighborSet_eq_degree,eq] at b
      omega
    have split := a.dist_outside tree.connected (Set.mem_range_self _) notIn (x := tip)
    have low := ecc ⟨tip,ne⟩
    rw [distances,(G.dist_comm (u:=z.val) (v:=tip)),split,(G.dist_comm (u:=tip) (v:=c))] at low
    change G.dist c tip = k+2 at dist
    have zero : G.dist c z.val = 0 := by omega
    exact ((tree.connected c z.val).dist_eq_zero_iff.mp zero).symm
  · intro eq
    have no : ¬G.Adj c v := by
      intro cv
      have q := noLeaf v cv
      rw [ncard_neighborSet_eq_degree,dv] at q
      omega
    refine ⟨?_,?_⟩
    · rw [degree_induce_compl_singleton_of_not_adj G z.property (eq ▸ no),eq]
      exact dc
    · intro x
      rw [distances,eq]
      exact upper _

private lemma swap_or_same (a b : Arm G c (n+1)) :
    ∃ e : G ≃g G, e c = c ∧ ∀ i, e (a.vertex i) = b.vertex i := by
  by_cases apart : ∀ i j, a.vertex i ≠ b.vertex j
  · exact swap_arms a b apart
  push Not at apart
  obtain ⟨s,t,m⟩ := apart
  have propagate {i j : Fin (n+1)} (w : (pathGraph (n+1)).Walk i j)
      (hi : a.vertex i ∈ Set.range b.vertex) : a.vertex j ∈ Set.range b.vertex := by
    induction w with
    | nil => exact hi
    | @cons i j k ad p ih =>
      apply ih
      by_contra out
      obtain ⟨l,e⟩ := hi
      have h := (a.internal i j).mpr (pathGraph_adj.mp ad)
      rw [←e] at h
      exact a.away j ((b.external l _ out).mp h).2
  have incl (i) : a.vertex i ∈ Set.range b.vertex :=
    propagate ((pathGraph_preconnected _ s i).some) ⟨t,m.symm⟩
  choose f eq using incl
  have inj : Function.Injective f := fun i j h =>
    a.vertex.injective (by rw [←eq i,←eq j,h])
  have edge (a : Arm G c (n+1)) : G.Adj (a.vertex 0) c :=
    (a.external 0 c (fun ⟨j,h⟩ => a.away j h)).mpr ⟨rfl,rfl⟩
  have f0 : f 0 = 0 := by
    apply Fin.ext
    apply ((b.external (f 0) c (fun ⟨j,h⟩ => b.away j h)).mp _).1
    rw [eq]; exact edge a
  have all (i : Fin (n+1)) : f i = i := by
    induction i using WellFoundedLT.induction with
    | _ i ih =>
      by_cases z : i.val=0
      · have : i=0 := Fin.ext z
        simpa [this] using f0
      · let j : Fin (n+1) := ⟨i.val-1,by omega⟩
        have ji : j < i := by change i.val-1 < i.val;omega
        have sj : j.val+1=i.val := by dsimp [j];omega
        have adj := (a.internal j i).mpr (Or.inl sj)
        rw [←eq j,←eq i,ih j ji] at adj
        rcases (b.internal j (f i)).mp adj with h|h
        · exact Fin.ext (h.symm.trans sj)
        · have lt : f i < i := by change (f i).val < i.val;omega
          have rep := ih (f i) lt
          have same := inj rep
          exact (Fin.ne_of_lt lt same).elim
  exact ⟨SimpleGraph.Iso.refl,rfl,fun i => by change a.vertex i=b.vertex i;rw [←eq i,all]⟩

private lemma extend_card {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {v : V} {w : W} (f : G.induce {v}ᶜ ≃g H.induce {w}ᶜ)
    (ad : ∀ x : ({v}ᶜ : Set V), G.Adj v x.val ↔ H.Adj w (f x).val) :
    Nonempty (G ≃g H) := by
  classical
  let map (x : V) : W := if h : x=v then w else (f ⟨x,h⟩).val
  let inv (y : W) : V := if h : y=w then v else (f.symm ⟨y,h⟩).val
  have mv : map v = w := by simp [map]
  have iw : inv w = v := by simp [inv]
  have mc (x : ({v}ᶜ : Set V)) : map x.val = (f x).val := by simp [map,show x.val ≠ v from x.property]
  have ic (y : ({w}ᶜ : Set W)) : inv y.val = (f.symm y).val := by simp [inv,show y.val ≠ w from y.property]
  refine ⟨{toFun := map, invFun := inv, left_inv := ?_, right_inv := ?_, map_rel_iff' := ?_}⟩
  · intro x
    by_cases h : x=v
    · simp [h,mv,iw]
    · change inv (map (⟨x,h⟩ : ({v}ᶜ : Set V)).val) = x
      rw [mc,ic]; simp
  · intro y
    by_cases h : y=w
    · simp [h,mv,iw]
    · change map (inv (⟨y,h⟩ : ({w}ᶜ : Set W)).val) = y
      rw [ic,mc]; simp
  · intro x y
    change H.Adj (map x) (map y) ↔ G.Adj x y
    by_cases hx : x=v <;> by_cases hy : y=v
    · simp [hx,hy]
    · subst x
      rw [mv,show map y = _ from mc ⟨y,hy⟩]
      exact (ad ⟨y,hy⟩).symm
    · subst y
      rw [mv,show map x = _ from mc ⟨x,hx⟩,H.adj_comm _ w,G.adj_comm _ v]
      exact (ad ⟨x,hx⟩).symm
    · rw [show map x = _ from mc ⟨x,hx⟩,show map y = _ from mc ⟨y,hy⟩]
      exact f.map_adj_iff

private def Arm.recenter {d : V} (a : Arm G c n) (e : c=d) : Arm G d n where
  vertex := a.vertex
  away i := by rw [←e];exact a.away i
  internal := a.internal
  external i x h := by rw [←e];exact a.external i x h

private lemma Arm.tip_deg [Fintype V] (a : Arm G c (n+2)) :
    G.degree (a.vertex (Fin.last (n+1))) = 1 := by
  apply degree_eq_one_iff_existsUnique_adj.mpr
  exact ⟨_,(a.tip_only _).mpr rfl,fun x h => (a.tip_only x).mp h⟩

private lemma match_radial_cards {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} {c : V} {d : W} {n : Nat} (a : Arm G c (n+2)) (b : Arm H d (n+2))
    (f : G.induce {a.vertex (Fin.last (n+1))}ᶜ ≃g H.induce {b.vertex (Fin.last (n+1))}ᶜ)
    (hub : f ⟨c,(a.away _).symm⟩ = ⟨d,(b.away _).symm⟩) : Nonempty (G ≃g H) := by
  let A := (a.shorten.map f).recenter hub
  let B := b.shorten
  obtain ⟨g,_,all⟩ := swap_or_same A B
  let e := f.trans g
  apply extend_card e
  intro x
  rw [a.tip_only,b.tip_only]
  let s := a.shorten.vertex (Fin.last n)
  let t := b.shorten.vertex (Fin.last n)
  have eq : e s=t := all (Fin.last n)
  change x.val = s.val ↔ (e x).val = t.val
  rw [←Subtype.ext_iff,←Subtype.ext_iff,←eq]
  exact e.injective.eq_iff.symm

private lemma match_radial {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} {c v : V} {d w : W} {k : Nat} (a : Arm G c (k+2)) (b : Arm H d (k+2))
    (av : a.vertex (Fin.last (k+1)) = v) (bw : b.vertex (Fin.last (k+1)) = w)
    (f : G.induce {v}ᶜ ≃g H.induce {w}ᶜ) {cv : c≠v} {dw : d≠w}
    (hub : f ⟨c,cv⟩ = ⟨d,dw⟩) : Nonempty (G ≃g H) := by
  subst v w
  exact match_radial_cards a b f hub

private noncomputable def level [Fintype V] (G : SimpleGraph V) (c : V) (r : Nat) : Finset V :=
  Finset.univ.filter (fun x => G.dist c x = r)

private lemma level_card_delete {V : Type} [Fintype V] (G : SimpleGraph V)
    (tr : G.IsTree) {c v : V} (dv : G.degree v = 1) (ne : c ≠ v) (r : Nat) :
    (level G c r).card =
      (level (G.induce {v}ᶜ) (⟨c,ne⟩ : ({v}ᶜ : Set V)) r).card +
        if G.dist c v = r then 1 else 0 := by
  classical
  let f : ({v}ᶜ : Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have eq : (level (G.induce {v}ᶜ) (⟨c,ne⟩ : ({v}ᶜ : Set V)) r).map f = (level G c r).erase v := by
    ext x
    rw [Finset.mem_map,Finset.mem_erase]
    have dist := induce_compl_singleton_dist_eq G tr (induce_compl_singleton_isTree_of_deg_one G tr dv)
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨y.property,?_⟩
      simpa [level,dist,f] using hy
    · rintro ⟨nx,hx⟩
      refine ⟨⟨x,nx⟩,?_,rfl⟩
      simpa [level,dist] using hx
  have card := congrArg Finset.card eq
  rw [Finset.card_map] at card
  rw [card]
  by_cases d : G.dist c v = r
  · have mem : v ∈ level G c r := by simpa [level] using d
    simp [d,Finset.card_erase_add_one mem]
  · have no : v ∉ level G c r := by simpa [level] using d
    simp [d,Finset.erase_eq_of_notMem no]

private lemma iso_dist {A B : Type*} {S : SimpleGraph A} {T : SimpleGraph B}
    (f : S ≃g T) (x y) : T.dist (f x) (f y) = S.dist x y :=
  congrArg ENat.toNat (iso_edist_eq _ _ _ x y)

private lemma size_level_iso {W : Type*} {H : SimpleGraph W} [Fintype V] [Fintype W]
    (f : G ≃g H) (c : V) (r : Nat) : (level G c r).card = (level H (f c) r).card := by
  classical
  apply Finset.card_bij' (fun x _ => f x) (fun y _ => f.symm y)
  · intro x hx
    simpa [level,iso_dist] using hx
  · intro y hy
    have z := iso_dist f c (f.symm y)
    simp at z
    simpa [level,z] using hy
  · simp
  · simp

private lemma iso_hubs {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} {c d v w} {r : Nat} (cv : c ≠ v) (dw : d ≠ w)
    (f : G.induce {v}ᶜ ≃g H.induce {w}ᶜ)
    (left : ∀ z : ({v}ᶜ : Set V), (3 ≤ (G.induce {v}ᶜ).degree z ∧
      ∀ x, (G.induce {v}ᶜ).dist z x ≤ r) ↔ z.val = c)
    (right : ∀ z : ({w}ᶜ : Set W), (3 ≤ (H.induce {w}ᶜ).degree z ∧
      ∀ x, (H.induce {w}ᶜ).dist z x ≤ r) ↔ z.val = d) :
    f ⟨c,cv⟩ = ⟨d,dw⟩ := by
  let z : ({v}ᶜ : Set V) := ⟨c,cv⟩
  have L := (left z).mpr rfl
  apply Subtype.ext
  apply (right (f z)).mp
  refine ⟨?_,?_⟩
  · rw [f.degree_eq]
    exact L.1
  · intro y
    obtain ⟨x,rfl⟩ := f.surjective y
    rw [iso_dist]
    exact L.2 x

end TreeArms
end OMA

section Solution
open SimpleGraph OMA.TreeArms Classical

theorem OMA.solution : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1.H3 := by
  intro V W _ _ _ G H σ tg th cards deg bg r c d hr dg dh eg eh _ _ _ _ nlG nlH smallG smallH
  obtain ⟨k,rfl⟩ : ∃ k, r=k+2 := ⟨r-2,by omega⟩
  have bh : ∃ w, 3 ≤ (H.neighborSet w).ncard := by
    obtain ⟨v,bv⟩ := bg
    exact ⟨σ v,by rwa [←deg]⟩
  obtain ⟨dc,upG,tipG⟩ := hub_and_tips G tg c k dg eg smallG bg
  obtain ⟨dd,upH,tipH⟩ := hub_and_tips H th d k dh eh smallH bh
  have deg' (v) : G.degree v = H.degree (σ v) := by
    simpa only [ncard_neighborSet_eq_degree] using deg v
  let f (v) := (cards v).some
  have neqG (v) (leaf : G.degree v=1) : c ≠ v := by rintro rfl;omega
  have neqH (v) (leaf : G.degree v=1) : d ≠ σ v := by
    have := deg' v
    intro eq
    rw [eq] at dd
    omega
  have rooted (v) (leaf : G.degree v=1) :
      f v ⟨c,neqG v leaf⟩ = ⟨d,neqH v leaf⟩ := by
    apply iso_hubs _ _ (f v)
    · exact hub_card G tg c v k dc leaf nlG upG (tipG v)
    · exact hub_card H th d (σ v) k dd ((deg' v).symm.trans leaf) nlH upH (tipH (σ v))
  have bal (v) (leaf : G.degree v=1) :
      (level G c (k+2)).card + (if H.dist d (σ v)=k+2 then 1 else 0)
      = (level H d (k+2)).card + (if G.dist c v=k+2 then 1 else 0) := by
    have l := level_card_delete G tg leaf (neqG v leaf) (k+2)
    have r := level_card_delete H th ((deg' v).symm.trans leaf) (neqH v leaf) (k+2)
    have s := size_level_iso (f v) (⟨c,neqG v leaf⟩ : ({v}ᶜ : Set V)) (k+2)
    rw [rooted v leaf] at s
    omega
  obtain ⟨a,_,far⟩ := tipG c
  let v := a.vertex (Fin.last (k+1))
  change G.dist c v=k+2 at far
  obtain ⟨b,_,far'⟩ := tipH d
  let u := σ.symm (b.vertex (Fin.last (k+1)))
  have eu : σ u = b.vertex (Fin.last (k+1)) := σ.apply_symm_apply _
  have ul : G.degree u=1 := by rw [deg',eu,b.tip_deg]
  have balG := bal v a.tip_deg
  have balH := bal u ul
  rw [if_pos far] at balG
  rw [eu,if_pos far'] at balH
  have radial : H.dist d (σ v) = k+2 := by
    by_contra bad
    rw [if_neg bad] at balG
    split at balH <;> omega
  obtain ⟨arm,endpt⟩ := max_arm H th.connected d (σ v) (k+1) radial smallH
  exact match_radial a arm rfl endpt (f v) (rooted v a.tip_deg)

end Solution
