import OMAReductions.R_Erdos713_erdos_713_parts_i_R1_H2_R1

-- Credit: @zarnab222-dev

/-!
A forbidden linear forest on q vertices embeds in the path on q vertices.
Consequently every host avoiding the forest has bounded depth. A sufficiently
large such host contains a nonempty piece with q interchangeable copies over
a common boundary. Any number of copies still avoids the forest because a
forbidden copy can meet at most q bodies.

If one such piece contributes more than a edges per vertex, repeating the
piece and padding with isolated vertices gives the required eventual lower
bound. Otherwise deleting pieces preserves an upper bound of a*n plus a
constant. This rules out arbitrarily large hosts above the higher slope b.
-/
/-! A path-length bound gives a recursive decomposition into connected pieces
with one root removed at each level. -/
open SimpleGraph Finset
open scoped Classical
namespace E713Depth
def CutConnected {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧ ∀ T ⊆ S, T.Nonempty → T ≠ S → ∃ u ∈ T, ∃ v ∈ S, v ∉ T ∧ G.Adj u v

theorem propagate {V : Type*} (G : SimpleGraph V) (T : Finset V)
    (closed : ∀ u ∈ T, ∀ v, G.Adj u v → v ∈ T) {u v} (hu : u ∈ T) (reach : G.Reachable u v) : v ∈ T := by
  obtain ⟨p⟩ := reach
  induction p with
  | nil => exact hu
  | cons h _ ih => exact ih (closed _ hu _ h)

theorem partition {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    ∃ P : Finset (Finset V), P.biUnion id=S ∧ (P : Set (Finset V)).PairwiseDisjoint id ∧
    (∀ T ∈ P, CutConnected G T) ∧
    ∀ T ∈ P, ∀ u ∈ T, ∀ v ∈ S, G.Adj u v → v ∈ T := by
  classical
  let X : SimpleGraph V := { Adj := fun u v => G.Adj u v ∧ u ∈ S ∧ v ∈ S
                             symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
                             loopless := ⟨fun _ h => h.1.ne rfl⟩ }
  let B (u : V) := S.filter (X.Reachable u)
  let P := S.image B
  have root (u) (hu : u ∈ S) : u ∈ B u := mem_filter.mpr ⟨hu,Reachable.refl _⟩
  have stable {u v} (edge : X.Reachable u v) : B u=B v := by
    ext w
    simp only [B,mem_filter]
    exact and_congr_right fun _ => ⟨fun h => edge.symm.trans h,fun h => edge.trans h⟩
  have inside {u v} (hu : v ∈ B u) : v ∈ S := (mem_filter.mp hu).1
  have closed (u) (v) (hv : v ∈ B u) (w) (hw : w ∈ S) (vw : G.Adj v w) : w ∈ B u :=
    mem_filter.mpr ⟨hw,(mem_filter.mp hv).2.trans (show X.Adj v w from ⟨vw,inside hv,hw⟩).reachable⟩
  refine ⟨P,?_,?_,?_,?_⟩
  · ext v
    constructor
    · intro h
      obtain ⟨_,ht,hv⟩ := mem_biUnion.mp h
      obtain ⟨u,_,rfl⟩ := mem_image.mp ht
      exact inside hv
    · intro h
      exact mem_biUnion.mpr ⟨B v,mem_image_of_mem _ h,root _ h⟩
  · intro a ha b hb ne
    obtain ⟨u,_,rfl⟩ := mem_image.mp ha
    obtain ⟨v,_,rfl⟩ := mem_image.mp hb
    refine Finset.disjoint_left.mpr fun w hw hw' => ?_
    exact ne (stable ((mem_filter.mp hw).2.trans (mem_filter.mp hw').2.symm))
  · intro t ht
    obtain ⟨u,hu,rfl⟩ := mem_image.mp ht
    refine ⟨⟨u,root _ hu⟩,?_⟩
    intro T sub nonempty ne
    obtain ⟨x,hx⟩ := nonempty
    by_contra! barrier
    have cl (v) (hv : v ∈ T) (w) (e : X.Adj v w) : w ∈ T := by
      by_contra miss
      exact barrier v hv w (closed _ _ (sub hv) _ e.2.2 e.1) miss e.1
    apply ne (Subset.antisymm sub ?_)
    intro v hv
    exact propagate X T cl hx ((mem_filter.mp (sub hx)).2.symm.trans (mem_filter.mp hv).2)
  · intro t ht
    obtain ⟨u,_,rfl⟩ := mem_image.mp ht
    exact closed u

def depth {V : Type*} [DecidableEq V] (G : SimpleGraph V) : ℕ → Finset V → Prop
  | 0, S => S=∅
  | d+1, S => ∃ P : Finset (Finset V), P.biUnion id=S ∧ (P : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ T ∈ P, ∀ u ∈ T, ∀ v ∈ S, G.Adj u v → v ∈ T) ∧
      ∀ T ∈ P, ∃ r ∈ T, depth G d (T.erase r)

theorem depth_from_path {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (q : ℕ)
    (short : ∀ {a b} (p : G.Walk a b), p.IsPath → p.length+1 < q) :
    depth G q univ := by
  classical
  have descend (d : ℕ) {a b : V} (p : G.Walk a b) (hp : p.IsPath) (T : Finset V)
      (conn : CutConnected G T) (endB : b ∈ T)
      (avoid : ∀ x ∈ T, x ∈ p.support → x=b) (room : d+p.length+1 ≥ q) :
      depth G d (T.erase b) := by
    induction d generalizing a b T with
    | zero => have := short p hp; omega
    | succ d ih =>
      obtain ⟨P,cover,sep,connected,closed⟩ := partition G (T.erase b)
      refine ⟨P,cover,sep,closed,?_⟩
      intro U hU
      have sub : U ⊆ T.erase b := fun _ hx => cover ▸ mem_biUnion.mpr ⟨U,hU,hx⟩
      have proper : U ≠ T := fun e => (mem_erase.mp (sub (e ▸ endB))).1 rfl
      obtain ⟨v,hv,w,hw,miss,e⟩ := conn.2 U (sub.trans (erase_subset b T)) (connected U hU).1 proper
      have eq : w=b := by
        by_contra ne
        exact miss (closed U hU v hv w (mem_erase.mpr ⟨ne,hw⟩) e)
      subst w
      have fresh : v ∉ p.support := fun h => (mem_erase.mp (sub hv)).1 (avoid v (mem_of_mem_erase (sub hv)) h)
      refine ⟨v,hv,ih (p.concat e.symm) ((Walk.concat_isPath_iff _).mpr ⟨hp,fresh⟩) U (connected U hU) hv ?_ ?_⟩
      · intro x hx mem
        rw [Walk.support_concat] at mem
        simp only [List.mem_append,List.mem_singleton] at mem
        exact mem.resolve_left (fun h => (mem_erase.mp (sub hx)).1 (avoid x (mem_of_mem_erase (sub hx)) h))
      · rw [Walk.length_concat]; omega
  cases q with
  | zero =>
    apply eq_empty_iff_forall_notMem.mpr
    intro v _
    have := short (Walk.nil (u:=v)) (by simp)
    omega
  | succ q =>
    obtain ⟨P,cover,sep,conn,closed⟩ := partition G univ
    refine ⟨P,cover,sep,closed,?_⟩
    intro T hT
    obtain ⟨v,hv⟩ := (conn T hT).1
    exact ⟨v,hv,descend q (Walk.nil (u:=v)) (by simp) T (conn T hT) hv (by simp) (by simp)⟩
end E713Depth
namespace E713Repeat

def fan {A W : Type*} (H : SimpleGraph A) (P : SimpleGraph W) (attach : A → W → Prop) (I : Type*) :
    SimpleGraph (A ⊕ (I × W)) where
  Adj x y := match x,y with
    | .inl a,.inl b => H.Adj a b
    | .inl a,.inr (_,v) | .inr (_,v),.inl a => attach a v
    | .inr (i,u),.inr (j,v) => i=j ∧ P.Adj u v
  symm := ⟨by rintro (a|⟨i,u⟩) (b|⟨j,v⟩) hab
              · exact hab.symm
              · exact hab
              · exact hab
              · exact ⟨hab.1.symm,hab.2.symm⟩⟩
  loopless := ⟨by rintro (a|⟨i,u⟩)
                  · exact H.loopless.irrefl a
                  · exact fun h => h.2.ne rfl⟩

theorem exclude_all {V A W I : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (H : SimpleGraph A) (P : SimpleGraph W) (attach : A → W → Prop)
    (free : G.Free (fan H P attach (Fin (Fintype.card V)))) :
    G.Free (fan H P attach I) := by
  classical
  rintro ⟨e⟩
  let indices (u : V) : Finset I := match e u with
    | .inl _ => ∅
    | .inr (i,_) => {i}
  let T := univ.biUnion indices
  have per (u : V) : (indices u).card ≤ 1 := by
    unfold indices
    cases e u <;> simp
  have total : T.card ≤ Fintype.card V := by
    calc T.card ≤ ∑ u, (indices u).card := card_biUnion_le
         _ ≤ ∑ _ : V, 1 := sum_le_sum (fun u _ => per u)
         _ = _ := by simp
  let code : T ↪ Fin (Fintype.card V) := T.equivFin.toEmbedding.trans (Fin.castLEEmb total)
  have used (u : V) {i : I} {w : W} (eq : e u=Sum.inr (i,w)) : i ∈ T := by
    apply mem_biUnion.mpr
    exact ⟨u,mem_univ _,by simp [indices,eq]⟩
  let index (i : I) : Fin (Fintype.card V) := if h : i ∈ T then code ⟨i,h⟩ else ⟨0,Fintype.card_pos⟩
  let cast (x : A ⊕ (I × W)) : A ⊕ (Fin (Fintype.card V) × W) := match x with
    | .inl a => .inl a
    | .inr (i,w) => .inr (index i,w)
  have hom {x y} (xy : (fan H P attach I).Adj x y) : (fan H P attach _).Adj (cast x) (cast y) := by
    rcases x with a | ⟨i,w⟩ <;> rcases y with b | ⟨j,z⟩
    · exact xy
    · exact xy
    · exact xy
    · exact ⟨congrArg index xy.1,xy.2⟩
  apply free
  refine ⟨⟨⟨fun u => cast (e u),fun h => hom (e.toHom.map_rel' h)⟩,?_⟩⟩
  intro u v eq
  apply e.injective
  change cast (e u) = cast (e v) at eq
  cases eu : e u with
  | inl a =>
    cases ev : e v with
    | inl b => exact congrArg Sum.inl (Sum.inl.inj (by simpa only [eu,ev,cast] using eq : Sum.inl a = (Sum.inl b : A ⊕ (Fin (Fintype.card V) × W))))
    | inr p => rcases p with ⟨i,w⟩; simp [eu,ev,cast] at eq
  | inr p =>
    obtain ⟨i,w⟩ := p
    cases ev : e v with
    | inl a => simp [eu,ev,cast] at eq
    | inr p =>
      obtain ⟨j,z⟩ := p
      rw [eu,ev] at eq
      change Sum.inr (index i,w) = (Sum.inr (index j,z) : A ⊕ _) at eq
      obtain ⟨ij,wz⟩ := Prod.mk.inj (Sum.inr.inj eq)
      simp only [index,used u eu,used v ev,↓reduceDIte] at ij
      exact congrArg Sum.inr (Prod.ext (congrArg Subtype.val (code.injective ij)) wz)

noncomputable def mass {A W : Type*} [Fintype A] [Fintype W] (P : SimpleGraph W)
    (attach : A → W → Prop) : ℕ :=
  (∑ a : A, (univ.filter (attach a)).card) +
  ∑ w : W, ((univ.filter fun a => attach a w).card + P.degree w)

theorem count {A W I : Type*} [Fintype A] [Fintype W] [Fintype I]
    (H : SimpleGraph A) (P : SimpleGraph W) (attach : A → W → Prop) :
    2*(fan H P attach I).edgeFinset.card = 2*H.edgeFinset.card + Fintype.card I * mass P attach := by
  classical
  let X := fan H P attach I
  let L (a : A) := univ.filter (attach a)
  let R (w : W) := univ.filter fun a => attach a w
  have left (a : A) : X.neighborFinset (.inl a) = (H.neighborFinset a).disjSum (univ ×ˢ L a) := by
    ext v
    rw [X.mem_neighborFinset]
    cases v with
    | inl b => simp [SimpleGraph.mem_neighborFinset,X,fan]
    | inr x => obtain ⟨i,w⟩ := x; simp [X,fan,L]
  have right (i : I) (w : W) : X.neighborFinset (.inr (i,w)) =
      (R w).disjSum (({i}:Finset I) ×ˢ P.neighborFinset w) := by
    ext v
    rw [X.mem_neighborFinset]
    cases v with
    | inl a => simp [X,fan,R]
    | inr x => obtain ⟨j,z⟩ := x; simp [SimpleGraph.mem_neighborFinset,X,fan,eq_comm,and_comm]
  have dl (a : A) : X.degree (.inl a) = H.degree a + Fintype.card I*(L a).card := by
    rw [← X.card_neighborFinset_eq_degree,left,card_disjSum,card_product,card_univ,H.card_neighborFinset_eq_degree]
  have dr (i : I) (w : W) : X.degree (.inr (i,w)) = (R w).card + P.degree w := by
    rw [← X.card_neighborFinset_eq_degree,right,card_disjSum,card_product]
    simp
  change 2*X.edgeFinset.card = _
  rw [← X.sum_degrees_eq_twice_card_edges,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [dl,dr,sum_add_distrib,← mul_sum,sum_const,card_univ,smul_eq_mul,
    H.sum_degrees_eq_twice_card_edges]
  unfold mass
  simp only [sum_add_distrib]
  change _ = 2*H.edgeFinset.card + Fintype.card I*((∑ a, (L a).card) + ((∑ w,(R w).card)+∑ w,P.degree w))
  ring

end E713Repeat
namespace E713Types

abbrev Shape (q M : ℕ) := (s : Fin (M+1)) × (SimpleGraph (Fin s.val) × (Fin q → Fin s.val → Bool))

def Models {V : Type*} (G : SimpleGraph V) (B : Finset V) {q M : ℕ} (idx : B ↪ Fin q)
    (s : Shape q M) (T : Finset V) : Prop :=
  ∃ e : T ≃ Fin s.1.val,
    (∀ x y : T, G.Adj x.val y.val ↔ s.2.1.Adj (e x) (e y)) ∧
    ∀ b : B, ∀ x : T, G.Adj b.val x.val ↔ s.2.2 (idx b) (e x) = true

theorem model_exists {V : Type*} (G : SimpleGraph V) (B T : Finset V) {q M : ℕ}
    (idx : B ↪ Fin q) (small : T.card ≤ M) : ∃ s : Shape q M, Models G B idx s T := by
  classical
  let e := T.equivFin
  let P : SimpleGraph (Fin T.card) := (G.induce (T : Set V)).comap e.symm
  let lab (i : Fin q) (j : Fin T.card) := decide (∃ b : B, idx b=i ∧ G.Adj b.val (e.symm j).val)
  refine ⟨⟨⟨T.card,by omega⟩,P,lab⟩,e,?_,?_⟩
  · intro x y
    change G.Adj x.val y.val ↔ G.Adj (e.symm (e x)).val (e.symm (e y)).val
    simp
  · intro b x
    change G.Adj b.val x.val ↔ lab (idx b) (e x)=true
    simp [lab]

theorem translate {V : Type*} (G : SimpleGraph V) (B U T : Finset V) {q M : ℕ} (idx : B ↪ Fin q)
    {s : Shape q M} (a : Models G B idx s U) (b : Models G B idx s T) :
    ∃ e : U ≃ T, (∀ x y : U, G.Adj x.val y.val ↔ G.Adj (e x).val (e y).val) ∧
      ∀ z : B, ∀ x : U, G.Adj z.val x.val ↔ G.Adj z.val (e x).val := by
  obtain ⟨i,gi,ai⟩ := a
  obtain ⟨j,gj,aj⟩ := b
  refine ⟨i.trans j.symm,?_,?_⟩
  · intro x y
    exact (gi x y).trans (by simpa using (gj (j.symm (i x)) (j.symm (i y))).symm)
  · intro z x
    exact (ai z x).trans (by simpa using (aj z (j.symm (i x))).symm)

noncomputable def number (q M : ℕ) := Fintype.card (Shape q M)

theorem many_models {V : Type*} (G : SimpleGraph V) (B : Finset V) (P : Finset (Finset V)) (q M k : ℕ)
    (boundary : B.card ≤ q) (small : ∀ T ∈ P, T.card ≤ M)
    (large : number q M*k < P.card) :
    ∃ U ∈ P, ∃ T : Fin (k+1) ↪ P,
      ∀ i, ∃ e : U ≃ (T i).val,
        (∀ x y : U, G.Adj x.val y.val ↔ G.Adj (e x).val (e y).val) ∧
        ∀ z : B, ∀ x : U, G.Adj z.val x.val ↔ G.Adj z.val (e x).val := by
  classical
  let idx := B.equivFin.toEmbedding.trans (Fin.castLEEmb boundary)
  choose sig model using (fun t : P => model_exists G B t.val idx (small _ t.property))
  let F (s : Shape q M) := univ.filter fun t : P => sig t=s
  have mass : P.card = ∑ s : Shape q M, (F s).card := by
    have map : Set.MapsTo sig (univ : Finset P) (univ : Finset (Shape q M)) := fun _ _ => mem_univ _
    simpa only [card_univ,Fintype.card_coe] using card_eq_sum_card_fiberwise map
  obtain ⟨s,rich⟩ : ∃ s, k < (F s).card := by
    by_contra! all
    have bound := sum_le_sum (s := univ) (fun s _ => all s)
    simp only [sum_const,card_univ,smul_eq_mul,← mass] at bound
    exact (not_lt_of_ge bound) large
  let emb : Fin (k+1) ↪ F s := (Fin.castLEEmb rich).trans (F s).equivFin.symm.toEmbedding
  let T : Fin (k+1) ↪ P := emb.trans (Function.Embedding.subtype _)
  have sigT (i) : sig (T i)=s := (mem_filter.mp (emb i).property).2
  have ok (i) : Models G B idx s (T i).val := sigT i ▸ model (T i)
  exact ⟨(T 0).val,(T 0).property,T,fun i => translate G B _ _ idx (ok 0) (ok i)⟩

noncomputable def piece {V : Type*} (G : SimpleGraph V) (B U : Finset V) (I : Type*) :=
  E713Repeat.fan (⊥ : SimpleGraph B) (G.induce (U : Set V)) (fun b u => G.Adj b.val u.val) I

theorem copy_fan {V I : Type*} (G : SimpleGraph V) (B U : Finset V) (P : Finset (Finset V))
    (sep : (P : Set (Finset V)).PairwiseDisjoint id)
    (away : ∀ T ∈ P, Disjoint B T) (T : I ↪ P)
    (same : ∀ i, ∃ e : U ≃ (T i).val, (∀ x y : U, G.Adj x.val y.val ↔ G.Adj (e x).val (e y).val) ∧
      ∀ z : B, ∀ x : U, G.Adj z.val x.val ↔ G.Adj z.val (e x).val) :
    piece G B U I ⊑ G := by
  classical
  choose e internal external using same
  let f (v : B ⊕ (I × U)) : V := match v with
    | .inl b => b.val
    | .inr (i,x) => (e i x).val
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · rintro (a|⟨i,x⟩) (b|⟨j,y⟩) h
    · exact h.elim
    · exact (external j a y).mp h
    · exact ((external i b x).mp h).symm
    · obtain ⟨rfl,hxy⟩ := h
      exact (internal i x y).mp hxy
  · rintro (a|⟨i,x⟩) (b|⟨j,y⟩) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · change a.val = (e j y).val at h
      exact (Finset.disjoint_left.mp (away _ (T j).property) a.property (h.symm ▸ (e j y).property)).elim
    · change (e i x).val = b.val at h
      exact (Finset.disjoint_left.mp (away _ (T i).property) b.property (h ▸ (e i x).property)).elim
    · change (e i x).val=(e j y).val at h
      have ij : i=j := by
        by_contra ne
        have neq : (T i).val ≠ (T j).val := fun h => ne (T.injective (Subtype.ext h))
        exact Finset.disjoint_left.mp (sep (T i).property (T j).property neq) (e i x).property (h.symm ▸ (e j y).property)
      subst j
      exact congrArg (fun z => Sum.inr (i,z)) ((e i).injective (Subtype.ext h))

noncomputable def limit (q k : ℕ) : ℕ → ℕ
  | 0 => 0
  | d+1 => (limit q k d + 1) * (number q (limit q k d + 1) * k)

theorem extract {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (q k : ℕ) :
    ∀ d (S A : Finset V), E713Depth.depth G d S → A.card+d ≤ q → Disjoint A S →
      (∀ u ∈ S, ∀ v ∉ S, G.Adj u v → v ∈ A) → limit q k d < S.card →
      ∃ B U : Finset V, U.Nonempty ∧ U ⊆ S ∧ Disjoint B U ∧
        (∀ u ∈ U, ∀ v ∉ U, G.Adj u v → v ∈ B) ∧ piece G B U (Fin (k+1)) ⊑ G := by
  classical
  intro d
  induction d with
  | zero =>
    rintro S A rfl _ _ _ big
    simp at big
  | succ d ih =>
    intro S A depth budget dis outside huge
    obtain ⟨P,cover,sep,closed,roots⟩ := depth
    have sub (U) (hu : U ∈ P) : U ⊆ S := fun x hx => cover ▸ mem_biUnion.mpr ⟨U,hu,hx⟩
    by_cases heavy : ∃ T ∈ P, limit q k d+1 < T.card
    · obtain ⟨T,ht,large⟩ := heavy
      obtain ⟨r,hr,next⟩ := roots T ht
      have sz := card_erase_add_one hr
      have gap : limit q k d < (T.erase r).card := by omega
      have space : (insert r A).card+d ≤ q := by have h := card_insert_le r A; omega
      have apart : Disjoint (insert r A) (T.erase r) := by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hy
        rcases mem_insert.mp hx with eq | ax
        · exact (mem_erase.mp hy).1 eq
        · exact Finset.disjoint_left.mp dis ax (sub _ ht (mem_of_mem_erase hy))
      have out (u) (hu : u ∈ T.erase r) (v) (hv : v ∉ T.erase r) (edge : G.Adj u v) : v ∈ insert r A := by
        by_cases eq : v=r
        · simp [eq]
        have nT : v ∉ T := fun h => hv (mem_erase.mpr ⟨eq,h⟩)
        have nS : v ∉ S := fun h => nT (closed T ht _ (mem_of_mem_erase hu) v h edge)
        exact mem_insert_of_mem (outside u (sub _ ht (mem_of_mem_erase hu)) v nS edge)
      obtain ⟨B,U,nU,inc,sep',edges,copy⟩ := ih (T.erase r) (insert r A) next space apart out gap
      exact ⟨B,U,nU,inc.trans ((erase_subset r T).trans (sub T ht)),sep',edges,copy⟩
    · push Not at heavy
      let M := limit q k d+1
      have many : number q M*k < P.card := by
        by_contra! few
        have cap := sum_le_sum (s := P) (fun t ht => heavy t ht)
        rw [sum_const,smul_eq_mul] at cap
        have sum := card_biUnion_le (s := P) (t := id)
        rw [cover] at sum
        have small := Nat.mul_le_mul_right M few
        have cmp : S.card ≤ number q M*k*M := sum.trans (cap.trans small)
        change M*(number q M*k)<S.card at huge
        rw [Nat.mul_comm M] at huge
        omega
      obtain ⟨U,hU,T,same⟩ := many_models G A P q M k (by omega) heavy many
      obtain ⟨r,hr,_⟩ := roots U hU
      refine ⟨A,U,⟨r,hr⟩,sub U hU,dis.mono_right (sub U hU),?_,
        copy_fan G A U P sep (fun t ht => dis.mono_right (sub t ht)) T same⟩
      intro u hu v hv e
      exact outside u (sub U hU hu) v (fun h => hv (closed U hU u hu v h e)) e

end E713Types
/-! Every linear forest admits an ordering in which its edges join consecutive vertices. -/
open SimpleGraph Finset
open scoped Classical
namespace E713Linear
private theorem forest_leaf {W : Type*} [Fintype W] [Nonempty W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (forest : G.IsAcyclic) : ∃ v, G.degree v ≤ 1 := by
  classical
  rcases subsingleton_or_nontrivial W with hs|hn
  · let _ := hs
    obtain ⟨v⟩ := ‹Nonempty W›
    exact ⟨v,by simp⟩
  let _ := hn
  obtain ⟨T,sub,_,tree⟩ := (connected_top (V := W)).exists_isTree_le_of_le_of_isAcyclic
    (show G ≤ ⊤ from le_top) forest
  obtain ⟨v,hv⟩ := tree.exists_vert_degree_one_of_nontrivial
  exact ⟨v,(G.degree_le_of_le sub).trans hv.le⟩


theorem first_leaf {V : Type*} [Fintype V] (G : SimpleGraph V) (forest : G.IsAcyclic)
    (S : Finset V) (hs : S.Nonempty) :
    ∃ u ∈ S, ∀ v ∈ S, ∀ w ∈ S, G.Adj u v → G.Adj u w → v=w := by
  classical
  obtain ⟨z,hz⟩ := hs
  have : Nonempty S := ⟨⟨z,hz⟩⟩
  let X := G.induce (S : Set V)
  obtain ⟨u,degree⟩ := forest_leaf X (forest.induce _)
  refine ⟨u.val,u.property,?_⟩
  intro v hv w hw ev ew
  have small : (X.neighborFinset u).card ≤ 1 := by simpa using degree
  have eq := card_le_one.mp small (⟨v,hv⟩:S) ((X.mem_neighborFinset _ _).mpr ev)
    (⟨w,hw⟩:S) ((X.mem_neighborFinset _ _).mpr ew)
  exact congrArg Subtype.val eq

theorem label_at_leaf {V : Type*} [Fintype V] (G : SimpleGraph V) (forest : G.IsAcyclic)
    (cap : ∀ v, G.degree v ≤ 2) (S : Finset V) (u : V) (hu : u ∈ S)
    (leaf : ∀ v ∈ S, ∀ w ∈ S, G.Adj u v → G.Adj u w → v=w) :
    ∃ f : V → ℕ, f u=0 ∧ Set.InjOn f (S : Set V) ∧ (∀ v ∈ S, f v < S.card) ∧
      ∀ a ∈ S, ∀ b ∈ S, G.Adj a b → f a+1=f b ∨ f b+1=f a := by
  classical
  induction S using Finset.strongInductionOn generalizing u with
  | _ S ih =>
    let T := S.erase u
    have sz : T.card+1=S.card := card_erase_add_one hu
    by_cases nonempty : T.Nonempty
    · have next : ∃ v ∈ T, (∀ z ∈ T, G.Adj u z → z=v) ∧
          ∀ a ∈ T, ∀ b ∈ T, G.Adj v a → G.Adj v b → a=b := by
        by_cases neighbor : ∃ z ∈ T, G.Adj u z
        · obtain ⟨z,hz,uz⟩ := neighbor
          refine ⟨z,hz,fun w hw uw => leaf _ (mem_of_mem_erase hw) _ (mem_of_mem_erase hz) uw uz,?_⟩
          have rem := card_erase_add_one ((G.mem_neighborFinset z u).mpr uz.symm)
          rw [G.card_neighborFinset_eq_degree] at rem
          have small : ((G.neighborFinset z).erase u).card ≤ 1 := by have := cap z; omega
          intro a ha b hb za zb
          exact card_le_one.mp small _ (mem_erase.mpr ⟨(mem_erase.mp ha).1,(G.mem_neighborFinset _ _).mpr za⟩)
            _ (mem_erase.mpr ⟨(mem_erase.mp hb).1,(G.mem_neighborFinset _ _).mpr zb⟩)
        · obtain ⟨v,hv,uniq⟩ := first_leaf G forest T nonempty
          exact ⟨v,hv,fun w hw e => (neighbor ⟨w,hw,e⟩).elim,uniq⟩
      obtain ⟨v,hv,succV,uniq⟩ := next
      obtain ⟨g,g0,inj,rangeG,agree⟩ := ih T (erase_ssubset hu) v hv uniq
      let f (a : V) := if a=u then 0 else g a+1
      have inn {a} (ha : a ∈ S) (ne : a ≠ u) : a ∈ T := mem_erase.mpr ⟨ne,ha⟩
      refine ⟨f,by simp [f],?_,?_,?_⟩
      · intro a ha b hb eq
        by_cases ac : a=u <;> by_cases bc : b=u <;> simp_all only [f,if_true,if_false,Nat.add_one_ne_zero,Nat.zero_ne_add_one,Nat.add_right_cancel_iff]
        exact inj (inn ha ac) (inn hb bc) eq
      · intro a ha
        by_cases e : a=u
        · simpa only [f,e,if_pos rfl] using (card_pos.mpr ⟨u,hu⟩ : 0<S.card)
        · have h := rangeG a (inn ha e); simp [f,e]; omega
      · intro a ha b hb ab
        by_cases ac : a=u
        · subst a
          have bc := ab.ne.symm
          have e := succV b (inn hb bc) ab
          exact Or.inl (by simp [f,bc,e ▸ g0])
        by_cases bc : b=u
        · subst b
          have e := succV a (inn ha ac) ab.symm
          exact Or.inr (by simp [f,ac,e ▸ g0])
        have old := agree a (inn ha ac) b (inn hb bc) ab
        simpa only [f,ac,bc,if_false,Nat.add_right_cancel_iff] using old
    · have single : ∀ v ∈ S, v=u := by
        intro v hv
        by_contra ne
        exact nonempty ⟨v,mem_erase.mpr ⟨ne,hv⟩⟩
      exact ⟨fun _ => 0,rfl,fun a ha b hb _ => (single a ha).trans (single b hb).symm,
        fun _ _ => card_pos.mpr ⟨u,hu⟩,fun a ha b hb ab => (ab.ne ((single a ha).trans (single b hb).symm)).elim⟩

theorem contained_in_path {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (forest : G.IsAcyclic) (cap : ∀ v, G.degree v ≤ 2) : G ⊑ pathGraph (Fintype.card V) := by
  classical
  obtain ⟨u,hu,leaf⟩ := first_leaf G forest univ univ_nonempty
  obtain ⟨g,_,inj,rangeG,edge⟩ := label_at_leaf G forest cap univ u hu leaf
  let f (v : V) : Fin (Fintype.card V) := ⟨g v,by simpa using rangeG v (mem_univ _)⟩
  exact ⟨⟨⟨f,fun ab => pathGraph_adj.mpr (edge _ (mem_univ _) _ (mem_univ _) ab)⟩,
    fun _ _ eq => inj (mem_univ _) (mem_univ _) (congrArg Fin.val eq)⟩⟩

theorem bound_paths {V W : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (forest : G.IsAcyclic) (cap : ∀ v, G.degree v ≤ 2) (X : SimpleGraph W) (free : G.Free X)
    {a b : W} (p : X.Walk a b) (simple : p.IsPath) : p.length+1 < Fintype.card V := by
  classical
  by_contra! enough
  let e := Fin.castLEEmb enough
  have sub : pathGraph (Fintype.card V) ⊑ pathGraph (p.length+1) :=
    ⟨⟨⟨e,fun h => pathGraph_adj.mpr ((pathGraph_adj (n := Fintype.card V)).mp h)⟩,e.injective⟩⟩
  exact free (((contained_in_path G forest cap).trans sub).trans simple.isContained_pathGraph)
end E713Linear
namespace E713Peel

theorem filter_card {V : Type*} (S : Finset V) (p : V → Prop) :
    (univ.filter (fun x : S => p x.val)).card = (S.filter p).card := by
  classical
  change (S.attach.filter _).card = _
  rw [Finset.filter_attach p S,card_map,card_attach]

theorem sum_on {V : Type*} (S : Finset V) (f : V → ℕ) : (∑ v : S, f v.val) = ∑ v ∈ S, f v :=
  Finset.sum_attach S f

theorem peel {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (B U : Finset V)
    (dis : Disjoint B U) (out : ∀ u ∈ U, ∀ v ∉ U, G.Adj u v → v ∈ B) :
    2*G.edgeFinset.card = 2*(G.induce (↑(Uᶜ) : Set V)).edgeFinset.card +
      E713Repeat.mass (G.induce (U : Set V)) (fun (b : B) (u : U) => G.Adj b.val u.val) := by
  classical
  let deg (T : Finset V) (v : V) := (T.filter (G.Adj v)).card
  have subdeg (T : Finset V) (x : T) : (G.induce (T : Set V)).degree x = deg T x.val := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have eq : (G.induce (T : Set V)).neighborFinset x = univ.filter (fun y : T => G.Adj x.val y.val) := by
      ext y
      simp [SimpleGraph.mem_neighborFinset]
    exact eq ▸ filter_card T (G.Adj x.val)
  have split (v : V) : G.degree v = deg U v + deg Uᶜ v := by
    have eq : U.filter (G.Adj v) ∪ Uᶜ.filter (G.Adj v) = G.neighborFinset v := by
      ext w
      simp [SimpleGraph.mem_neighborFinset]
      tauto
    have ds : Disjoint (U.filter (G.Adj v)) (Uᶜ.filter (G.Adj v)) :=
      Finset.disjoint_left.mpr fun w hw ht => (mem_compl.mp (mem_filter.mp ht).1) (mem_filter.mp hw).1
    rw [← G.card_neighborFinset_eq_degree,← eq,card_union_of_disjoint ds]
  have inc : B ⊆ Uᶜ := fun _ hv => mem_compl.mpr fun hu => Finset.disjoint_left.mp dis hv hu
  have internal (u) (hu : u ∈ U) : deg Uᶜ u = deg B u := by
    apply congrArg Finset.card
    ext v
    simp only [mem_filter,mem_compl]
    exact ⟨fun h => ⟨out u hu v h.1 h.2,h.2⟩,fun h => ⟨mem_compl.mp (inc h.1),h.2⟩⟩
  have cross : (∑ v ∈ B, deg U v) = ∑ v ∈ Uᶜ, deg U v := by
    apply sum_subset inc
    intro v hv nb
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact nb (out u (mem_filter.mp hu).1 v (mem_compl.mp hv) (mem_filter.mp hu).2.symm)
  have once (T : Finset V) : 2*(G.induce (T : Set V)).edgeFinset.card = ∑ v ∈ T, deg T v := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
    simp_rw [subdeg]
    exact sum_on _ _
  have left (b : B) : (univ.filter (fun u : U => G.Adj b.val u.val)).card = deg U b.val := filter_card _ _
  have right (u : U) : (univ.filter (fun b : B => G.Adj b.val u.val)).card = deg B u.val := by
    calc _ = (univ.filter (fun b : B => G.Adj u.val b.val)).card := by
           congr 1
           ext b
           simp [SimpleGraph.adj_comm]
         _ = _ := filter_card _ _
  rw [once,← G.sum_degrees_eq_twice_card_edges,← U.sum_add_sum_compl]
  simp_rw [split]
  have massEq : E713Repeat.mass (G.induce (U : Set V)) (fun (b : B) (u : U) => G.Adj b.val u.val) =
      (∑ b ∈ B, deg U b) + ((∑ u ∈ U, deg B u) + ∑ u ∈ U, deg U u) := by
    unfold E713Repeat.mass
    rw [sum_add_distrib]
    apply congrArg₂ Nat.add
    · exact (sum_congr rfl (fun b _ => left b)).trans (sum_on B (deg U))
    · apply congrArg₂ Nat.add
      · exact (sum_congr rfl (fun u _ => right u)).trans (sum_on U (deg B))
      · exact (sum_congr rfl (fun u _ => subdeg U u)).trans (sum_on U (deg U))
  rw [massEq]
  simp only [sum_add_distrib]
  have mid : (∑ x ∈ U, deg Uᶜ x) = ∑ x ∈ U, deg B x := sum_congr rfl internal
  rw [mid,← cross]
  ring

end E713Peel
namespace E713Amplify
theorem padding {V W : Type*} [Fintype W] (G : SimpleGraph V) (active : ∀ v, ¬G.IsIsolated v)
    (X : SimpleGraph W) (free : G.Free X) (m : ℕ) (fit : Fintype.card W ≤ m) :
    X.edgeFinset.card ≤ extremalNumber m G := by
  classical
  let k := m-Fintype.card W
  let Z := X ⊕g (⊥ : SimpleGraph (Fin k))
  have hf : G.Free Z := by
    rintro ⟨e⟩
    have original (v : V) : ∃ w : W, e v = Sum.inl w := by
      cases h : e v with
      | inl w => exact ⟨w,rfl⟩
      | inr i =>
        obtain ⟨u,adj⟩ := exists_adj_iff_not_isIsolated.mpr (active v)
        have a := e.toHom.map_rel' adj
        change Z.Adj (e v) (e u) at a
        rw [h] at a
        cases hu : e u with
        | inl t => rw [hu] at a; exact (not_adj_sum_inl_inr t i a.symm).elim
        | inr j => rw [hu] at a; exact (sum_adj_inr.mp a).elim
    choose f he using original
    apply free
    refine ⟨⟨⟨f,?_⟩,?_⟩⟩
    · intro a b adj
      have h := e.toHom.map_rel' adj
      change Z.Adj (e a) (e b) at h
      rw [he a,he b] at h
      exact sum_adj_inl.mp h
    · intro a b eq
      exact e.injective ((he a).trans ((congrArg Sum.inl eq).trans (he b).symm))
  have sumedges : Z.edgeFinset.card=X.edgeFinset.card := by
    simp only [Z,edgeFinset_card]
    have eq := Fintype.card_congr (edgeSetSumEquiv (G:=X) (H:=(⊥ : SimpleGraph (Fin k))))
    simpa using eq
  have hh := card_edgeFinset_le_extremalNumber hf
  have sz : Fintype.card (W ⊕ Fin k)=m := by simp [k,fit]
  simpa only [sumedges,sz] using hh


theorem eventual (h s e : ℕ) (hs : 0 < s) (a : ℚ) (ha : 0 < a)
    (gap : 2*a*s < e) (f : ℕ → ℕ) (lower : ∀ m ≥ h, ((m-h)/s)*e ≤ 2*f m) :
    ∃ M, ∀ m ≥ M, a*m ≤ (f m : ℚ) := by
  obtain ⟨k,hk⟩ := exists_nat_gt ((2*a*(h+s))/(e-2*a*s))
  have pos : 0 < (e:ℚ)-2*a*s := sub_pos.mpr gap
  have pay := (div_lt_iff₀ pos).mp hk
  refine ⟨h+s*k,?_⟩
  intro m hm
  let l := (m-h)/s
  have fit : h ≤ m := by omega
  have kl : k ≤ l := (Nat.le_div_iff_mul_le hs).mpr (by rw [Nat.mul_comm]; omega)
  have tail := Nat.mod_lt (m-h) hs
  have div := Nat.mod_add_div (m-h) s
  have endpt : m ≤ h+l*s+s := by dsimp [l]; rw [Nat.mul_comm ((m-h)/s)]; omega
  have endQ : (m:ℚ) ≤ h+(l:ℚ)*s+s := by exact_mod_cast endpt
  have low : (l:ℚ)*e ≤ 2*(f m:ℚ) := by exact_mod_cast lower m fit
  have ge : (k:ℚ) ≤ l := by exact_mod_cast kl
  nlinarith [mul_le_mul_of_nonneg_left endQ ha.le, mul_le_mul_of_nonneg_right ge pos.le]

theorem amplify {V W : Type*} [Fintype V] [Nonempty V] [Fintype W] (F : SimpleGraph V)
    (active : ∀ v, ¬F.IsIsolated v) (X : SimpleGraph W) (free : F.Free X) (B U : Finset W)
    (hu : U.Nonempty) (copy : E713Types.piece X B U (Fin (Fintype.card V)) ⊑ X)
    (a : ℚ) (ha : 0 < a) (gain : 2*a*U.card <
      (E713Repeat.mass (X.induce (U : Set W)) (fun (b : B) (u : U) => X.Adj b.val u.val) : ℚ)) :
    ∃ M, ∀ m ≥ M, a*m ≤ (extremalNumber m F : ℚ) := by
  classical
  let e := E713Repeat.mass (X.induce (U : Set W)) (fun (b : B) (u : U) => X.Adj b.val u.val)
  apply eventual B.card U.card e (card_pos.mpr hu) a ha gain
  intro m hm
  let l := (m-B.card)/U.card
  let Y := E713Types.piece X B U (Fin l)
  have fr : F.Free Y := E713Repeat.exclude_all F _ _ _ (fun f => free (f.trans copy))
  have fit : Fintype.card (B ⊕ (Fin l × U)) ≤ m := by
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe]
    have h := Nat.div_mul_le_self (m-B.card) U.card
    dsimp [l]
    omega
  have upper := padding F active Y fr m fit
  have eq : 2*Y.edgeFinset.card = 2*(⊥ : SimpleGraph B).edgeFinset.card + l*e := by
    calc _ = 2*(⊥ : SimpleGraph B).edgeFinset.card + Fintype.card (Fin l)*e := by
           convert! E713Repeat.count (I:=Fin l) (⊥ : SimpleGraph B) (X.induce (U : Set W))
             (fun (b : B) (u : U) => X.Adj b.val u.val) using 1 <;> congr! 3
           ext z
           simp only [SimpleGraph.mem_edgeFinset]
         _ = _ := by rw [Fintype.card_fin]
  change l*e ≤ _
  omega

end E713Amplify
namespace E713Linear

theorem density (q : ℕ) (F : SimpleGraph (Fin q)) (forest : F.IsAcyclic)
    (active : ∀ v, ¬ F.IsIsolated v) (ne : ∃ v, 2 ≤ F.degree v) (cap : ∀ v, F.degree v ≤ 2)
    (a b : ℚ) (ab : a < b) (high : ∀ N, ∃ n ≥ N, b*n < (extremalNumber n F : ℚ)) :
    ∃ M, ∀ m ≥ M, a*m ≤ (extremalNumber m F : ℚ) := by
  classical
  by_cases ha : a ≤ 0
  · exact ⟨0,fun m _ => (mul_nonpos_of_nonpos_of_nonneg ha (Nat.cast_nonneg _)).trans (Nat.cast_nonneg _)⟩
  have pos : 0 < a := lt_of_not_ge ha
  obtain ⟨v,hv⟩ := ne
  let : Nonempty (Fin q) := ⟨v⟩
  have nbot : F ≠ ⊥ := by
    rintro rfl
    simp at hv
  have qq : q-1+1=q := by have := v.isLt; omega
  let L := E713Types.limit q (q-1) q
  let C := L.choose 2
  by_contra bad
  have bound (n : ℕ) : ∀ (W : Type) [Fintype W] (X : SimpleGraph W), Fintype.card W = n → F.Free X →
      (X.edgeFinset.card : ℚ) ≤ a*n+C := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W inst X sz free
      by_cases small : n ≤ L
      · have base := (card_edgeFinset_le_card_choose_two (G:=X)).trans (Nat.choose_le_choose 2 (sz ▸ small))
        have hq : (X.edgeFinset.card : ℚ) ≤ C := by exact_mod_cast base
        linarith [mul_nonneg pos.le (Nat.cast_nonneg n : (0:ℚ) ≤ n)]
      have short {x y} (p : X.Walk x y) (h : p.IsPath) : p.length+1 < q := by
        simpa using bound_paths F forest cap X free p h
      have dp := E713Depth.depth_from_path X q (fun p h => short p h)
      obtain ⟨B,U,hu,_,dis,out,copies⟩ := E713Types.extract X q (q-1) q univ ∅ dp
        (by simp) (by simp) (by simp) (by simpa only [card_univ,sz] using lt_of_not_ge small)
      rw [qq] at copies
      let mass := E713Repeat.mass (X.induce (U : Set W)) (fun (b : B) (u : U) => X.Adj b.val u.val)
      have cost : (mass : ℚ) ≤ 2*a*U.card := by
        by_contra! profitable
        exact bad (E713Amplify.amplify F active X free B U hu (by rw [Fintype.card_fin]; exact copies) a pos profitable)
      have eq := E713Peel.peel X B U dis out
      let R := Uᶜ
      let Y := X.induce (R : Set W)
      have sub : Y ⊑ X := ⟨⟨⟨Subtype.val,fun h => h⟩,Subtype.val_injective⟩⟩
      have fr : F.Free Y := fun ff => free (ff.trans sub)
      have total : R.card+U.card=n := by simp [R,card_compl,sz,Nat.sub_add_cancel (show U.card ≤ n from sz ▸ card_le_univ U)]
      have drop : R.card<n := by have := card_pos.mpr hu; omega
      have remain := ih R.card drop R Y (Fintype.card_coe R) fr
      have eqQ : 2*(X.edgeFinset.card : ℚ) = 2*(Y.edgeFinset.card : ℚ)+mass := by exact_mod_cast eq
      have sumQ : (R.card : ℚ)+U.card=n := by exact_mod_cast total
      apply (mul_le_mul_iff_right₀ (show (0:ℚ)<2 by norm_num)).mp
      calc 2*(X.edgeFinset.card:ℚ) = 2*(Y.edgeFinset.card:ℚ)+mass := eqQ
           _ ≤ 2*(a*R.card+C)+2*a*U.card := by
             apply add_le_add _ cost
             apply mul_le_mul_of_nonneg_left _ (by norm_num)
             convert! remain using 1 <;> congr! 3
           _ = 2*(a*n+C) := by rw [← sumQ]; ring
  obtain ⟨N,hN⟩ := exists_nat_gt ((C:ℚ)/(b-a))
  obtain ⟨n,hn,ex⟩ := high N
  obtain ⟨X,_,ext⟩ := exists_isExtremal_free (V:=Fin n) nbot
  obtain ⟨fr,eq⟩ := isExtremal_free_iff.mp ext
  have hb := bound n (Fin n) X (Fintype.card_fin n) fr
  have link : X.edgeFinset.card = extremalNumber n F := by
    convert! eq using 1 <;> simp
  have capN : (extremalNumber n F : ℚ) ≤ a*n+C := by
    calc _ = (X.edgeFinset.card : ℚ) := by exact_mod_cast link.symm
         _ ≤ _ := by convert! hb using 1 <;> congr! 3
  have enough := (div_lt_iff₀ (sub_pos.mpr ab)).mp (hN.trans_le (show (N:ℚ) ≤ n by exact_mod_cast hn))
  linarith

end E713Linear

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_i_R1_H2_R1.H1 := by
  intro q F _ forest _ active _ vertex cap a b gap high
  exact E713Linear.density q F forest active vertex cap a b gap high
