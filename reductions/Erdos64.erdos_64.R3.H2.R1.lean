import OMAReductions.R_Erdos64_erdos_64_R3
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Option

/-! Suppress the degree-two root of a leaf block. Both resulting problems concern a
strictly smaller graph with a marked edge. If the two neighbours were already
adjacent, the original edge survives and either endpoint may have degree two.
Otherwise the new edge restores the two degrees, and an unchanged cycle must
avoid it. In either case a marked cycle one edge short can be expanded at the root. -/
namespace OMA.R_Erdos64_erdos_64_R3_H2_R1
open SimpleGraph
open scoped Classical

def H1 : Prop :=
  ∀ (V : Type) (K : SimpleGraph V) [Fintype V] [DecidableRel K.Adj] (a b : V),
    K.Adj b a → 3 ≤ K.minDegree →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (K).Adj x y) →
    ∃ (k : ℕ) (v : V) (c : K.Walk v v), 2 ≤ k ∧ c.IsCycle ∧
      ((c.length = 2^k ∧ s(b,a) ∉ c.edges) ∨ (c.length + 1 = 2^k ∧ s(b,a) ∈ c.edges))

def H2 : Prop :=
  ∀ (V : Type) (K : SimpleGraph V) [Fintype V] [DecidableRel K.Adj] (a b : V),
    K.Adj b a → (∀ x, 2 ≤ K.degree x) → (∀ x, x ≠ a → x ≠ b → 3 ≤ K.degree x) →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (K).Adj x y) →
    ∃ (k : ℕ) (v : V) (c : K.Walk v v), 2 ≤ k ∧ c.IsCycle ∧
      (c.length = 2^k ∨ (c.length + 1 = 2^k ∧ s(b,a) ∈ c.edges))

variable {V : Type*} {G : SimpleGraph V} {r : V}

theorem closePath {G : SimpleGraph V} {r a b : V} (ha : G.Adj r a)
    (hb : G.Adj r b) (p : G.Walk a b) (hp : p.IsPath) (hr : r ∉ p.support)
    (hab : a ≠ b) :
    ∃ c : G.Walk r r, c.IsCycle ∧ c.length = p.length + 2 := by
  have hlen : 0 < p.length := by
    by_contra! h
    exact hab ((Walk.length_eq_zero_iff.mp (by omega : p.length = 0)).eq)
  refine ⟨.cons ha (p.concat hb.symm), ?_, by simp [Nat.add_assoc]⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · rw [Walk.tail_cons]
    exact (Walk.isPath_copy _ _ _).mpr (hp.concat hr hb.symm)
  · simp only [Walk.length_cons, Walk.length_concat]
    omega

theorem degreeTwo_neighbours (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (r : V) (hr : G.degree r = 2) :
    ∃ a b : ({v : V | v ≠ r} : Set V), a ≠ b ∧ G.Adj r a.val ∧ G.Adj r b.val ∧
      ∀ z : ({v : V | v ≠ r} : Set V), G.Adj r z.val → z = a ∨ z = b := by
  classical
  have hcard : (G.neighborFinset r).card = 2 := (G.card_neighborFinset_eq_degree r).trans hr
  obtain ⟨x, y, hxy, he⟩ := Finset.card_eq_two.mp hcard
  have hadj (z : V) : G.Adj r z ↔ z = x ∨ z = y := by
    rw [← G.mem_neighborFinset, he]
    simp
  have hx := (hadj x).mpr (Or.inl rfl)
  have hy := (hadj y).mpr (Or.inr rfl)
  let a : ({v : V | v ≠ r} : Set V) := ⟨x, hx.ne.symm⟩
  let b : ({v : V | v ≠ r} : Set V) := ⟨y, hy.ne.symm⟩
  have hab : a ≠ b := fun h => hxy (congrArg Subtype.val h)
  refine ⟨a, b, hab, hx, hy, ?_⟩
  intro z hz
  exact ((hadj z.val).mp hz).imp Subtype.ext Subtype.ext

theorem orientAt {K : SimpleGraph V} {a b : V} {c : K.Walk b b}
    (hc : c.IsCycle) (hs : c.snd = a) :
    ∃ (h : K.Adj b a) (p : K.Walk a b), (Walk.cons h p).IsCycle ∧
      (Walk.cons h p).length = c.length := by
  cases c with
  | nil => exact (hc.not_nil Walk.Nil.nil).elim
  | cons h p =>
    simp only [Walk.snd_cons] at hs
    subst a
    exact ⟨h, p, hc, rfl⟩

theorem through_iff_first (K : SimpleGraph V) (a b : V) (n : ℕ) :
    (∃ v, ∃ c : K.Walk v v, c.IsCycle ∧ c.length = n ∧ s(b,a) ∈ c.edges) ↔ ∃ (h : K.Adj b a) (p : K.Walk a b),
      (Walk.cons h p).IsCycle ∧ (Walk.cons h p).length = n := by
  classical
  constructor
  · rintro ⟨v, c, hc, hn, he⟩
    have hb := c.fst_mem_support_of_mem_edges he
    let w := c.rotate b hb
    have hw : w.IsCycle := hc.rotate hb
    have hlen : w.length = n := (c.length_rotate b hb).trans hn
    have hew : s(b, a) ∈ w.edges := (c.rotate_edges b hb).perm.mem_iff.mpr he
    clear_value w
    cases w with
    | nil => exact (hw.not_nil Walk.Nil.nil).elim
    | @cons _ x _ h q =>
      rw [Walk.edges_cons, List.mem_cons] at hew
      rcases hew with head | tail
      · have hax : a = x := by
          simp only [Sym2.eq, Sym2.rel_iff'] at head
          grind
        subst x
        exact ⟨h,q,hw,hlen⟩
      · have hq := ((q.cons_isCycle_iff h).mp hw).1
        have heq : a = q.penultimate := hq.eq_penultimate_of_mem_edges tail
        have hrev : (Walk.cons h q).reverse.snd = a := by
          rw [Walk.snd_reverse, Walk.penultimate_cons_of_not_nil h q (Walk.not_nil_of_isCycle_cons hw),
            ← heq]
        obtain ⟨h', p, hp, hl⟩ := orientAt hw.reverse hrev
        exact ⟨h', p, hp, hl.trans (((Walk.cons h q).length_reverse).trans hlen)⟩
  · rintro ⟨h,p,hp,hl⟩
    exact ⟨b, .cons h p, hp, hl, by simp⟩

theorem forgetAddedEdge {F : SimpleGraph V} {a b : V}
    {u v : V} (q : (F ⊔ fromEdgeSet {s(b,a)}).Walk u v) (he : s(b,a) ∉ q.edges) :
    ∀ e, e ∈ q.edges → e ∈ F.edgeSet := by
  intro e h
  have hz := q.edges_subset_edgeSet h
  rw [edgeSet_sup, edgeSet_fromEdgeSet] at hz
  rcases hz with hf | hf
  · exact hf
  · exact (he ((Set.mem_singleton_iff.mp hf.1) ▸ h)).elim

theorem adjacent_or_mark {F : SimpleGraph V} {a b x y : V} (hab : a ≠ b) :
    (F ⊔ fromEdgeSet {s(b,a)}).Adj x y ↔ F.Adj x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  change F.Adj x y ∨ _ ↔ _
  rw [fromEdgeSet_adj, Set.mem_singleton_iff]
  simp only [Sym2.eq, Sym2.rel_iff']
  grind

theorem suppress_noCut (a b : ({v : V | v ≠ r} : Set V)) (hab : a ≠ b)
    (only : ∀ z : ({v : V | v ≠ r} : Set V), G.Adj r z.val → z = a ∨ z = b) (cuts : (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G).Adj x y)) :
    (∀ (z : ↥(({v : V | v ≠ r} : Set V))) (S : Set ↥(({v : V | v ≠ r} : Set V))), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G.induce (({v : V | v ≠ r} : Set V)) ⊔ fromEdgeSet {s(b,a)}).Adj x y) := by
  classical
  let K := G.induce (({v : V | v ≠ r} : Set V)) ⊔ fromEdgeSet {s(b,a)}
  intro z S hz left right
  let t := if a = z then b else a
  have ht : t = a ∨ t = b := by by_cases h : a = z <;> simp [t,h]
  have tz : t ≠ z := by
    by_cases h : a = z
    · intro eq; exact hab (h.trans (eq.symm.trans (if_pos h : t = b)))
    · simpa only [t,if_neg h] using h
  let proj (v : V) : ({v : V | v ≠ r} : Set V) := if h : v = r then t else ⟨v,h⟩
  have orig (v : ({v : V | v ≠ r} : Set V)) : proj v.val = v := by
    have vr : v.val ≠ r := v.property
    exact dif_neg vr
  have root : proj r = t := by simp [proj]
  have fiber (v : V) (h : proj v = z) : v = z.val := by
    by_cases vr : v = r
    · exact (tz ((vr ▸ root : proj v = t).symm.trans h)).elim
    · exact congrArg Subtype.val ((orig ⟨v,vr⟩).symm.trans h)
  have fromRoot (w : ({v : V | v ≠ r} : Set V)) (hw : G.Adj r w.val) : t = w ∨ K.Adj t w := by
    change t = w ∨ ((G.induce (({v : V | v ≠ r} : Set V))) ⊔ fromEdgeSet {s(b,a)}).Adj t w
    rw [adjacent_or_mark hab]
    rcases ht with h | h <;> rcases only w hw with h' | h' <;> grind
  have edge (x y : V) (hxy : G.Adj x y) : proj x = proj y ∨ K.Adj (proj x) (proj y) := by
    by_cases xr : x = r
    · subst x
      have yr := hxy.ne.symm
      rw [root, orig ⟨y,yr⟩]
      exact fromRoot ⟨y,yr⟩ hxy
    by_cases yr : y = r
    · subst y
      rw [root, orig ⟨x,xr⟩]
      exact (fromRoot ⟨x,xr⟩ hxy.symm).imp Eq.symm (fun h => h.symm)
    rw [orig ⟨x,xr⟩, orig ⟨y,yr⟩]
    exact Or.inr (Or.inl hxy)
  let T : Set V := {v | proj v ∈ S}
  obtain ⟨l,hl,hlz⟩ := left
  obtain ⟨d,hd⟩ := right
  have liftSet (w : ({v : V | v ≠ r} : Set V)) : w.val ∈ T ↔ w ∈ S := by change proj w.val ∈ S ↔ _; rw [orig]
  obtain ⟨x,hx,hxz,y,hy,adj⟩ := cuts z.val T ((liftSet z).mpr hz)
    ⟨l.val,(liftSet l).mpr hl,fun h => hlz (Subtype.ext h)⟩ ⟨d.val,fun h => hd ((liftSet d).mp h)⟩
  have xs : proj x ∈ S := hx
  have ys : proj y ∉ S := hy
  exact ⟨proj x,xs,fun h => hxz (fiber x h),proj y,ys,
    (edge x y adj).resolve_left (fun h => ys (h ▸ xs))⟩

theorem degree_loss_one [Fintype V] [DecidableRel G.Adj] (x : ({v : V | v ≠ r} : Set V)) :
    G.degree x.val ≤ (G.induce (({v : V | v ≠ r} : Set V))).degree x + 1 := by
  classical
  let F := G.induce (({v : V | v ≠ r} : Set V))
  let f (v : G.neighborSet x.val) : Option (F.neighborSet x) :=
    if hr : v.val = r then none else some ⟨⟨v.val,hr⟩,v.property⟩
  have inj : Function.Injective f := by
    intro v w eq
    apply Subtype.ext
    by_cases hv : v.val = r <;> by_cases hw : w.val = r
    · exact hv.trans hw.symm
    · simp [f,hv,hw] at eq
    · simp [f,hv,hw] at eq
    · have he : (⟨⟨v.val,hv⟩,v.property⟩ : F.neighborSet x) = ⟨⟨w.val,hw⟩,w.property⟩ :=
        Option.some.inj (by simpa only [f,dif_neg hv,dif_neg hw] using eq)
      exact congrArg (fun u : F.neighborSet x => u.val.val) he
  simpa only [Fintype.card_option,card_neighborSet_eq_degree] using Fintype.card_le_of_injective f inj

theorem suppression_high {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (a b : {v : V // v ≠ r}) (ab : a ≠ b)
    (only : ∀ v, G.Adj r v → v = a.val ∨ v = b.val)
    (nonedge : ¬G.Adj a.val b.val) (high : ∀ v, v ≠ r → 3 ≤ G.degree v) :
    let K := (G.induce {v : V | v ≠ r}) ⊔ SimpleGraph.fromEdgeSet {s(b,a)}
    ∀ x, 3 ≤ K.degree x := by
  classical
  let W := {v : V // v ≠ r}
  let K := (G.induce {v : V | v ≠ r}) ⊔ SimpleGraph.fromEdgeSet {s(b,a)}
  change ∀ x : W, 3 ≤ K.degree x
  intro x
  let target : W := if x = a then b else a
  have extra : K.Adj b a := Or.inr <| (SimpleGraph.fromEdgeSet_adj _).mpr ⟨rfl, ab.symm⟩
  have replacement (hr : G.Adj x.val r) : K.Adj x target ∧ ¬G.Adj x.val target.val := by
    rcases only _ hr.symm with h | h
    · have e : x = a := Subtype.ext h
      subst x
      simpa [target] using And.intro extra.symm nonedge
    · have e : x = b := Subtype.ext h
      subst x
      simpa [target, ab.symm] using And.intro extra (show ¬G.Adj b.val a.val from fun z => nonedge z.symm)
  let f (y : G.neighborSet x.val) : W := if h : y.val = r then target else ⟨y.val,h⟩
  have valid (y : G.neighborSet x.val) : K.Adj x (f y) := by
    by_cases h : y.val = r
    · have hr : G.Adj x.val r := by simpa only [← h] using (show G.Adj x.val y.val from y.property)
      simpa [f,h] using (replacement hr).1
    · simpa only [f, dif_neg h] using (show K.Adj x ⟨y.val,h⟩ from Or.inl y.property)
  have injective : Function.Injective f := by
    intro u v e
    apply Subtype.ext
    have h := congrArg Subtype.val e
    by_cases hu : u.val = r <;> by_cases hv : v.val = r
    · exact hu.trans hv.symm
    · have hr : G.Adj x.val r := by simpa only [← hu] using (show G.Adj x.val u.val from u.property)
      have k : target.val = v.val := by simpa [f,hu,hv] using h
      exact ((replacement hr).2 (by rw [k]; exact v.property)).elim
    · have hr : G.Adj x.val r := by simpa only [← hv] using (show G.Adj x.val v.val from v.property)
      have k : u.val = target.val := by simpa [f,hu,hv] using h
      exact ((replacement hr).2 (by rw [← k]; exact u.property)).elim
    · simpa [f, hu, hv] using h
  let g (y : G.neighborSet x.val) : K.neighborSet x := ⟨f y,valid y⟩
  have g_inj : Function.Injective g := fun _ _ h => injective (congrArg Subtype.val h)
  exact (high x.val x.property).trans <| by
    simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_le_of_injective g g_inj


theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R3.H2 := by
  intro solid deficient V G _ _ r rootDegree high cuts
  classical
  let W := {v : V | v ≠ r}
  let F := G.induce W
  obtain ⟨a,b,ab,ra,rb,only⟩ := degreeTwo_neighbours G r rootDegree
  let K := F ⊔ fromEdgeSet {s(b,a)}
  let proj := (Embedding.induce (G := G) W).toHom
  have onMark : K.Adj b a := (adjacent_or_mark ab).mpr (Or.inr (Or.inr ⟨rfl,rfl⟩))
  let NoSeparator (T : SimpleGraph (↥W)) :=
    ∀ (z : ↥W) (S : Set (↥W)), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, T.Adj x y
  have keepCuts : NoSeparator K := suppress_noCut a b ab only cuts
  let Goal := ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k
  have survives {v : ↥W} {k : ℕ} (c : F.Walk v v) (hk : 2 ≤ k) (hc : c.IsCycle)
      (len : c.length = 2^k) : Goal :=
    ⟨k,v.val,c.map proj,hk,hc.map Subtype.val_injective,(c.length_map proj).trans len⟩
  have expands {v : ↥W} {k : ℕ} (c : K.Walk v v) (hk : 2 ≤ k) (hc : c.IsCycle)
      (len : c.length + 1 = 2^k) (edge : s(b,a) ∈ c.edges) : Goal := by
    obtain ⟨e,p,hp,hl⟩ := (through_iff_first K a b c.length).mp ⟨v,c,hc,rfl,edge⟩
    obtain ⟨path,away⟩ := (Walk.cons_isCycle_iff p e).mp hp
    have valid := forgetAddedEdge (F := F) p away
    let q := (p.transfer F valid).map proj
    have qp : q.IsPath := (path.transfer valid).map Subtype.val_injective
    have avoids : r ∉ q.support := by
      rw [show q.support = (p.transfer F valid).support.map proj from (p.transfer F valid).support_map proj]
      rintro hit
      obtain ⟨x,_,hx⟩ := List.mem_map.mp hit
      exact x.property hx
    obtain ⟨d,hd,dl⟩ := closePath ra rb q qp avoids (fun h => ab (Subtype.ext h))
    have ql : q.length = p.length := ((p.transfer F valid).length_map proj).trans (p.length_transfer valid)
    rw [Walk.length_cons] at hl
    refine ⟨k,r,d,hk,hd,?_⟩
    calc
      d.length = q.length + 2 := dl
      _ = p.length + 2 := congrArg (· + 2) ql
      _ = 2^k := by omega
  by_cases existing : F.Adj b a
  · have equal : K = F := by
      ext x y
      rw [adjacent_or_mark ab]
      constructor
      · rintro (h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
        exacts [h,existing.symm,existing]
      · exact Or.inl
    have lower (x : ↥W) : 2 ≤ F.degree x := by
      have h : G.degree x.val ≤ F.degree x + 1 := degree_loss_one (G := G) (r := r) x
      have hh := high x.val x.property
      omega
    have others (x : ↥W) (xa : x ≠ a) (xb : x ≠ b) : 3 ≤ F.degree x := by
      have contained : G.neighborSet x.val ⊆ W := by
        rintro y hy he
        have xr : G.Adj x.val r := he ▸ hy
        exact (only x xr.symm).elim xa xb
      change 3 ≤ (G.induce W).degree x
      rw [degree_induce_of_neighborSet_subset contained]
      exact high x.val x.property
    obtain ⟨k,v,c,hk,hc,old | ⟨len,edge⟩⟩ := deficient _ F a b existing lower others
      ((congrArg NoSeparator equal).mp keepCuts)
    · exact survives c hk hc old
    · have includeF : F ≤ K := le_sup_left
      exact expands (c.mapLe includeF) hk (hc.mapLe includeF)
        (by simpa only [Walk.length_mapLe] using len)
        (by simpa only [Walk.edges_mapLe_eq_edges] using edge)
  · have only' (v : V) (rv : G.Adj r v) : v = a.val ∨ v = b.val :=
      (only ⟨v,rv.ne.symm⟩ rv).imp (congrArg Subtype.val) (congrArg Subtype.val)
    have nonedge : ¬ G.Adj a.val b.val := fun h => existing h.symm
    have : Nonempty (↥W) := ⟨a⟩
    have deg : 3 ≤ K.minDegree := K.le_minDegree_of_forall_le_degree 3
      (suppression_high G r a b ab only' nonedge high)
    obtain ⟨k,v,c,hk,hc,⟨len,away⟩ | ⟨len,edge⟩⟩ := solid _ K a b onMark deg keepCuts
    · have valid := forgetAddedEdge (F := F) c away
      exact survives (c.transfer F valid) hk (hc.transfer valid) ((c.length_transfer valid).trans len)
    · exact expands c hk hc len edge

end OMA.R_Erdos64_erdos_64_R3_H2_R1
