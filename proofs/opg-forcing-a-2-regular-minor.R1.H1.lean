import OMAReductions.R_opg_forcing_a_2_regular_minor_R1
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Sym

/-!
Dirac (1952): a 2-connected graph with minimum degree at least d has a cycle of length at least
min(n, 2d). Take a longest path x 0, ..., x m; S and T index the chords at its two ends.
A crossing pair of chords closes the path into a cycle through all vertices (this part and the
list-cycle lemmas are adapted from philipsaint's proof of Dirac's Hamiltonicity theorem).
If a neighbour of x m precedes a neighbour of x 0, a closest such pair gives a cycle of length at
least |S| + |T|. Otherwise every neighbour of x 0 precedes every neighbour of x m, and a chain of
bridges of the path, each chosen with maximal reach, gives such a cycle.
-/

namespace OMA.EG

open SimpleGraph

/-- Core (Dirac 1952): a 2-connected graph with minimum degree d has a cycle of length
at least min(n, 2d). 2-connectivity is stated as: any two vertices other than v are joined by
a walk avoiding v. -/
def CoreStatement : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ),
    2 ≤ d → 3 ≤ Fintype.card V → G.Connected →
    (∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support) →
    (∀ v, d ≤ G.degree v) →
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ min (Fintype.card V) (2 * d) ≤ c.length

namespace C1


open SimpleGraph

variable {V : Type} {G : SimpleGraph V}

def PL (G : SimpleGraph V) (a : V) (L : List V) (b : V) : Prop :=
  L.IsChain G.Adj ∧ L.head? = some a ∧ L.getLast? = some b

lemma PL.eq_cons {a b : V} {L : List V} (h : PL G a L b) : L = a :: L.tail := by
  obtain ⟨-, h2, -⟩ := h
  cases L with
  | nil => simp at h2
  | cons y L => simp at h2; simp [h2]

lemma PL.length_pos {a b : V} {L : List V} (h : PL G a L b) : 1 ≤ L.length := by
  rw [h.eq_cons]; simp

lemma PL.single (a : V) : PL G a [a] a := ⟨List.isChain_singleton _, rfl, rfl⟩

lemma PL.cons {a b c : V} {L : List V} (hab : G.Adj a b) (h : PL G b L c) :
    PL G a (a :: L) c := by
  obtain ⟨c1, hd, hl⟩ := h
  refine ⟨List.isChain_cons.2 ⟨?_, c1⟩, rfl, ?_⟩
  · intro y hy; rw [hd] at hy; cases hy; exact hab
  · rw [List.getLast?_cons, hl]; rfl

lemma PL.edge {a b : V} (hab : G.Adj a b) : PL G a [a, b] b := PL.cons hab (PL.single b)

lemma PL.append {a b c : V} {L M : List V} (h1 : PL G a L b) (h2 : PL G b M c) :
    PL G a (L ++ M.tail) c := by
  have hM := h2.eq_cons
  have hL := h1.eq_cons
  obtain ⟨c1, hd1, l1⟩ := h1
  obtain ⟨c2, hd2, l2⟩ := h2
  rw [hM] at c2 l2
  rw [List.isChain_cons] at c2
  refine ⟨?_, ?_, ?_⟩
  · rw [List.isChain_append]
    refine ⟨c1, c2.2, ?_⟩
    intro x hx y hy
    rw [l1] at hx; cases hx; exact c2.1 y hy
  · rw [hL]; simp
  · rw [List.getLast?_cons] at l2
    rw [List.getLast?_append]
    rcases h : M.tail.getLast? with _ | z
    · rw [h] at l2; simp at l2; simp [l1, l2]
    · rw [h] at l2; simp at l2; simp [l2]

lemma PL.reverse {a b : V} {L : List V} (h : PL G a L b) : PL G b L.reverse a := by
  obtain ⟨c1, hd, hl⟩ := h
  refine ⟨?_, by rw [List.head?_reverse, hl], by rw [List.getLast?_reverse, hd]⟩
  rw [List.isChain_reverse]
  exact c1.imp (fun _ _ h => h.symm)

lemma length_append_tail {L M : List V} (hM : 1 ≤ M.length) :
    (L ++ M.tail).length = L.length + M.length - 1 := by
  rw [List.length_append, List.length_tail]; omega

lemma mem_append_tail {L M : List V} {v : V} (h : v ∈ L ++ M.tail) : v ∈ L ∨ v ∈ M := by
  rcases List.mem_append.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_of_mem_tail h)

lemma nodup_append_tail {b c : V} {L M : List V} (hL : L.Nodup) (hM : M.Nodup)
    (h2 : PL G b M c) (hcap : ∀ v ∈ L, v ∈ M → v = b) : (L ++ M.tail).Nodup := by
  have hMe := h2.eq_cons
  rw [hMe, List.nodup_cons] at hM
  rw [List.nodup_append]
  refine ⟨hL, hM.2, ?_⟩
  intro v hv w hw hvw
  subst hvw
  have := hcap v hv (by rw [hMe]; exact List.mem_cons_of_mem _ hw)
  subst this
  exact hM.1 hw

/-! Closing a cyclic list into a cycle (adapted from philipsaint's Dirac proof). -/

lemma edge_not_mem {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hlen : 2 ≤ p.length) :
    s(u, v) ∉ p.edges := by
  cases p with
  | nil => simp at hlen
  | @cons _ w _ hadj p' =>
    intro hmem
    rw [Walk.edges_cons, List.mem_cons] at hmem
    have hnd := hp.support_nodup
    rw [Walk.support_cons, List.nodup_cons] at hnd
    rcases hmem with h | h
    · rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · subst h2
        have hp' : p'.IsPath := hp.of_cons
        have : p'.length = 0 := by
          rcases p' with _ | ⟨h'', p''⟩
          · rfl
          · exfalso
            have := hp'.support_nodup
            simp at this
        simp [this] at hlen
      · subst h1
        exact hadj.ne rfl
    · exact hnd.1 (Walk.fst_mem_support_of_mem_edges p' h)

lemma cycle_of_PL {a b : V} {c : List V} (hc : PL G a c b) (hba : G.Adj b a) (hnd : c.Nodup)
    (h3 : 3 ≤ c.length) : ∃ (u : V) (w : G.Walk u u), w.IsCycle ∧ w.length = c.length := by
  have hne : c ≠ [] := by
    rintro rfl
    simp at h3
  obtain ⟨hch, hhd, hlt⟩ := hc
  set W := Walk.ofSupport c hne hch
  have hW : W.support = c := Walk.support_ofSupport hne hch
  have hWl : W.length = c.length - 1 := Walk.length_ofSupport hne hch
  have hpath : W.IsPath := Walk.IsPath.mk' (by rw [hW]; exact hnd)
  have hadj : G.Adj (c.head hne) (c.getLast hne) := by
    have e1 : c.head hne = a := by
      rw [List.head?_eq_some_head hne] at hhd; exact Option.some.inj hhd
    have e2 : c.getLast hne = b := by
      rw [List.getLast?_eq_some_getLast hne] at hlt; exact Option.some.inj hlt
    rw [e1, e2]; exact hba.symm
  refine ⟨c.head hne, Walk.cons hadj W.reverse, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨hpath.reverse, ?_⟩
    rw [Walk.edges_reverse, List.mem_reverse]
    exact edge_not_mem W hpath (by omega)
  · rw [Walk.length_cons, Walk.length_reverse, hWl]
    omega

/-! Segments of the path `x 0, x 1, ..., x m`. -/

def seg (x : ℕ → V) (c d : ℕ) : List V := (List.range' c (d + 1 - c)).map x

variable (x : ℕ → V) (m : ℕ)

lemma mem_seg {c d : ℕ} {v : V} : v ∈ seg x c d ↔ ∃ k, c ≤ k ∧ k ≤ d ∧ x k = v := by
  simp only [seg, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨k, ⟨h1, h2⟩, h3⟩; exact ⟨k, h1, by omega, h3⟩
  · rintro ⟨k, h1, h2, h3⟩; exact ⟨k, ⟨h1, by omega⟩, h3⟩

lemma length_seg (c d : ℕ) : (seg x c d).length = d + 1 - c := by simp [seg]

lemma nodup_seg (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j) {c d : ℕ} (hd : d ≤ m) :
    (seg x c d).Nodup := by
  apply List.Nodup.map_on _ (List.nodup_range' _)
  intro i hi j hj hij
  rw [List.mem_range'_1] at hi hj
  exact hinj i j (by omega) (by omega) hij

lemma PL_range (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1))) :
    ∀ n c, c + n ≤ m → PL G (x c) ((List.range' c (n+1)).map x) (x (c+n)) := by
  intro n
  induction n with
  | zero => intro c _; simpa using PL.single (G := G) (x c)
  | succ n ih =>
    intro c hc
    rw [List.range'_succ, List.map_cons]
    have := ih (c+1) (by omega)
    rw [show c + 1 + n = c + (n+1) by omega] at this
    exact PL.cons (hadj c (by omega)) this

lemma PL_seg (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1))) {c d : ℕ} (hcd : c ≤ d)
    (hd : d ≤ m) : PL G (x c) (seg x c d) (x d) := by
  have := PL_range x m hadj (d - c) c (by omega)
  rw [show c + (d - c) = d by omega] at this
  unfold seg
  rw [show d + 1 - c = d - c + 1 by omega]
  exact this


/-! Bridges of the path. -/

def OnP (v : V) : Prop := ∃ k, k ≤ m ∧ x k = v

def Br (G : SimpleGraph V) (s t : ℕ) : Prop :=
  s ≤ m ∧ t ≤ m ∧ ∃ q : G.Walk (x s) (x t), ∀ z ∈ q.support, z = x s ∨ z = x t ∨ ¬ OnP x m z

def AT (G : SimpleGraph V) (p : ℕ) (v : V) : Prop :=
  ∃ q : G.Walk (x p) v, ∀ z ∈ q.support, z = x p ∨ ¬ OnP x m z

def AT' (G : SimpleGraph V) (v : V) (t : ℕ) : Prop :=
  ∃ q : G.Walk v (x t), ∀ z ∈ q.support, z = x t ∨ ¬ OnP x m z

lemma br_of_AT {p t : ℕ} {v : V} (h1 : AT x m G p v) (h2 : AT' x m G v t) (hp : p ≤ m)
    (ht : t ≤ m) : Br x m G p t := by
  obtain ⟨q1, hq1⟩ := h1
  obtain ⟨q2, hq2⟩ := h2
  refine ⟨hp, ht, q1.append q2, ?_⟩
  intro z hz
  rw [Walk.support_append] at hz
  rcases List.mem_append.1 hz with hz | hz
  · rcases hq1 z hz with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rcases hq2 z (List.mem_of_mem_tail hz) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

lemma bridge_aux (w : ℕ) (hwm : w < m) :
    ∀ (y y2 : V) (p : G.Walk y y2), y2 = x m → x w ∉ p.support →
      (∃ s t, s < w ∧ w < t ∧ Br x m G s t) ∨
      (∃ t, w < t ∧ t ≤ m ∧ ∃ q : G.Walk y (x t), ∀ z ∈ q.support, z = x t ∨ ¬ OnP x m z) := by
  intro y y2 p
  induction p with
  | nil =>
    intro he _
    subst he
    right
    exact ⟨m, hwm, le_rfl, Walk.nil, by simp⟩
  | @cons y y' _ hadj p ih =>
    intro he hw
    rw [Walk.support_cons, List.mem_cons, not_or] at hw
    rcases ih he hw.2 with h | ⟨t, hwt, htm, q, hq⟩
    · exact Or.inl h
    · by_cases hy : OnP x m y
      · obtain ⟨k, hkm, rfl⟩ := hy
        rcases Nat.lt_or_ge k w with hk | hk
        · left
          refine ⟨k, t, hk, hwt, by omega, htm, Walk.cons hadj q, ?_⟩
          intro z hz
          rw [Walk.support_cons, List.mem_cons] at hz
          rcases hz with hz | hz
          · exact Or.inl hz
          · exact Or.inr (hq z hz)
        · right
          have hkw : k ≠ w := by rintro rfl; exact hw.1 rfl
          exact ⟨k, by omega, hkm, Walk.nil, by simp⟩
      · right
        refine ⟨t, hwt, htm, Walk.cons hadj q, ?_⟩
        intro z hz
        rw [Walk.support_cons, List.mem_cons] at hz
        rcases hz with hz | hz
        · subst hz; exact Or.inr hy
        · exact hq z hz

lemma bridge_exists (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hconn : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support)
    {w : ℕ} (hw0 : 0 < w) (hwm : w < m) : ∃ s t, s < w ∧ w < t ∧ Br x m G s t := by
  obtain ⟨p, hp⟩ := hconn (x w) (x 0) (x m)
    (fun h => by have := hinj _ _ (by omega) (by omega) h; omega)
    (fun h => by have := hinj _ _ (by omega) (by omega) h; omega)
  rcases bridge_aux x m w hwm (x 0) _ p rfl hp with h | ⟨t, hwt, htm, q, hq⟩
  · exact h
  · exfalso
    rcases hq (x 0) (Walk.start_mem_support q) with h | h
    · have := hinj _ _ (by omega) htm h; omega
    · exact h ⟨0, by omega, rfl⟩

lemma max_bridge (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hconn : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support)
    {w : ℕ} (hw0 : 0 < w) (hwm : w < m) :
    ∃ s t, s < w ∧ w < t ∧ Br x m G s t ∧ ∀ p t', p < w → Br x m G p t' → t' ≤ t := by
  classical
  let P : ℕ → Prop := fun t => w < t ∧ ∃ s, s < w ∧ Br x m G s t
  obtain ⟨s0, t0, hs0, ht0, hb0⟩ := bridge_exists x m hinj hconn hw0 hwm
  have hP0 : P t0 := ⟨ht0, s0, hs0, hb0⟩
  have hspec : P (Nat.findGreatest P m) := Nat.findGreatest_spec hb0.2.1 hP0
  obtain ⟨h1, s, hs, hb⟩ := hspec
  refine ⟨s, _, hs, h1, hb, ?_⟩
  intro p t' hp hb'
  rcases Nat.lt_or_ge w t' with h | h
  · exact Nat.le_findGreatest hb'.2.1 ⟨h, p, hp, hb'⟩
  · omega

lemma path_of_br {s t : ℕ} (hb : Br x m G s t) :
    ∃ Q : List V, PL G (x s) Q (x t) ∧ Q.Nodup ∧
      (∀ v ∈ Q, v = x s ∨ v = x t ∨ ¬ OnP x m v) ∧
      (∀ v ∈ Q, ¬ OnP x m v → AT x m G s v ∧ AT' x m G v t) := by
  classical
  obtain ⟨hs, ht, q, hq⟩ := hb
  set q' := q.bypass with hq'
  have hpath : q'.IsPath := Walk.bypass_isPath q
  have hsub : q'.support ⊆ q.support := Walk.support_bypass_subset_support q
  have hmem : ∀ z ∈ q'.support, z = x s ∨ z = x t ∨ ¬ OnP x m z := fun z hz => hq z (hsub hz)
  refine ⟨q'.support, ⟨Walk.isChain_adj_support q', ?_, ?_⟩, hpath.support_nodup, hmem, ?_⟩
  · rw [← Walk.cons_tail_support]; rfl
  · rw [List.getLast?_eq_some_getLast (Walk.support_ne_nil q'), Walk.getLast_support]
  · intro v hv hoff
    have hvs : x s ≠ v := fun h => hoff ⟨s, hs, h⟩
    have hvt : x t ≠ v := fun h => hoff ⟨t, ht, h⟩
    constructor
    · refine ⟨q'.takeUntil v hv, ?_⟩
      intro z hz
      have hz' := Walk.support_takeUntil_subset_support q' hv hz
      rcases hmem z hz' with h | h | h
      · exact Or.inl h
      · subst h
        exact absurd hz (Walk.endpoint_notMem_support_takeUntil hpath hv hvt)
      · exact Or.inr h
    · have hv' : v ∈ q'.reverse.support := by
        rw [Walk.support_reverse]; exact List.mem_reverse.2 hv
      refine ⟨(q'.reverse.takeUntil v hv').reverse, ?_⟩
      intro z hz
      rw [Walk.support_reverse, List.mem_reverse] at hz
      have hz' := Walk.support_takeUntil_subset_support q'.reverse hv' hz
      rw [Walk.support_reverse, List.mem_reverse] at hz'
      rcases hmem z hz' with h | h | h
      · subst h
        exact absurd hz (Walk.endpoint_notMem_support_takeUntil hpath.reverse hv' hvs)
      · exact Or.inl h
      · exact Or.inr h


/-! The chain of bridges (case where every neighbour of `x 0` precedes every neighbour of `x m`). -/

def Inv (G : SimpleGraph V) (S T : Finset ℕ) (u w : ℕ) (L : List V) : Prop :=
  u < w ∧ w ≤ m ∧ (∀ k ∈ T, u ≤ k) ∧ (∀ p t, p < u → Br x m G p t → t ≤ w) ∧
  PL G (x u) L (x w) ∧ L.Nodup ∧
  (∀ v ∈ L, (∃ k, k ≤ u ∧ x k = v) ∨ v = x w ∨ (¬ OnP x m v ∧ ∃ p, p < u ∧ AT x m G p v)) ∧
  S.card + 1 ≤ L.length

lemma close_cycle (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1)))
    {S T : Finset ℕ} (hT : ∀ k ∈ T, k < m ∧ G.Adj (x k) (x m))
    {u w : ℕ} {L : List V} (hI : Inv x m G S T u w L) (hk : ∃ k ∈ T, k < w)
    (h3 : 3 ≤ S.card + T.card) :
    ∃ (y : V) (c : G.Walk y y), c.IsCycle ∧ S.card + T.card ≤ c.length := by
  classical
  obtain ⟨huw, hwm, hTu, -, hPL, hnd, hmem, hlen⟩ := hI
  obtain ⟨k0, hk0T, hk0w⟩ := hk
  have hne : (T.filter (· < w)).Nonempty := ⟨k0, Finset.mem_filter.2 ⟨hk0T, hk0w⟩⟩
  set j := (T.filter (· < w)).max' hne with hjdef
  have hjT : j ∈ T ∧ j < w := Finset.mem_filter.1 (Finset.max'_mem _ _)
  have hjmax : ∀ k ∈ T, k < w → k ≤ j := fun k hk hkw =>
    Finset.le_max' _ k (Finset.mem_filter.2 ⟨hk, hkw⟩)
  have huj : u ≤ j := hTu j hjT.1
  have P1 : PL G (x j) (seg x u j).reverse (x u) := (PL_seg x m hadj huj (by omega)).reverse
  have P3 : PL G (x w) (seg x w m) (x m) := PL_seg x m hadj hwm le_rfl
  have Q1 := P1.append hPL
  have Q2 := Q1.append P3
  have hnd1 : ((seg x u j).reverse ++ L.tail).Nodup := by
    refine nodup_append_tail (List.nodup_reverse.2 (nodup_seg x m hinj (by omega))) hnd hPL ?_
    intro v hv hvL
    obtain ⟨k, hk1, hk2, rfl⟩ := (mem_seg x).1 (List.mem_reverse.1 hv)
    rcases hmem _ hvL with ⟨k', hk', he⟩ | he | ⟨hoff, -⟩
    · have := hinj _ _ (by omega) (by omega) he
      have : k = u := by omega
      rw [this]
    · have := hinj _ _ (by omega) (by omega) he; omega
    · exact absurd ⟨k, by omega, rfl⟩ hoff
  have hnd2 : ((seg x u j).reverse ++ L.tail ++ (seg x w m).tail).Nodup := by
    refine nodup_append_tail hnd1 (nodup_seg x m hinj le_rfl) P3 ?_
    intro v hv hvs
    obtain ⟨k, hk1, hk2, rfl⟩ := (mem_seg x).1 hvs
    rcases mem_append_tail hv with hv | hvL
    · obtain ⟨k', hk1', hk2', he⟩ := (mem_seg x).1 (List.mem_reverse.1 hv)
      have := hinj _ _ (by omega) (by omega) he; omega
    · rcases hmem _ hvL with ⟨k', hk', he⟩ | he | ⟨hoff, -⟩
      · have := hinj _ _ (by omega) (by omega) he; omega
      · exact he
      · exact absurd ⟨k, by omega, rfl⟩ hoff
  have hTsub : T ⊆ Finset.Icc u j ∪ Finset.Ico w m := by
    intro k hk
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico]
    have := hTu k hk
    have := (hT k hk).1
    rcases Nat.lt_or_ge k w with h | h
    · have := hjmax k hk h; left; omega
    · right; omega
  have hTc := (Finset.card_le_card hTsub).trans (Finset.card_union_le _ _)
  rw [Nat.card_Icc, Nat.card_Ico] at hTc
  have hl1 := length_append_tail (L := (seg x u j).reverse) hPL.length_pos
  have hl2 := length_append_tail (L := (seg x u j).reverse ++ L.tail) P3.length_pos
  rw [List.length_reverse, length_seg] at hl1
  rw [length_seg] at hl2
  obtain ⟨y, c, hc, hcl⟩ := cycle_of_PL Q2 (hT j hjT.1).2.symm hnd2 (by omega)
  exact ⟨y, c, hc, by omega⟩

lemma chain_step (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1)))
    (hconn : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support)
    {S T : Finset ℕ} (hT : ∀ k ∈ T, k < m ∧ G.Adj (x k) (x m))
    {u w : ℕ} {L : List V} (hI : Inv x m G S T u w L) (hk : ∀ k ∈ T, w ≤ k)
    (hTne : T.Nonempty) : ∃ t L', w < t ∧ Inv x m G S T w t L' := by
  obtain ⟨huw, hwm, hTu, hRB, hPL, hnd, hmem, hlen⟩ := hI
  obtain ⟨k0, hk0⟩ := hTne
  have hwm' : w < m := lt_of_le_of_lt (hk k0 hk0) (hT k0 hk0).1
  obtain ⟨s, t, hsw, hwt, hb, hmax⟩ := max_bridge x m hinj hconn (by omega : 0 < w) hwm'
  have hus : u ≤ s := by
    by_contra h
    have := hRB s t (by omega) hb
    omega
  have htm : t ≤ m := hb.2.1
  obtain ⟨Q, hQPL, hQnd, hQmem, hQat⟩ := path_of_br x m hb
  have P2 : PL G (x u) (seg x u s) (x s) := PL_seg x m hadj hus (by omega)
  have D1 := hPL.reverse.append P2
  have D := D1.append hQPL
  have hnd1 : (L.reverse ++ (seg x u s).tail).Nodup := by
    refine nodup_append_tail (List.nodup_reverse.2 hnd) (nodup_seg x m hinj (by omega)) P2 ?_
    intro v hv hvs
    obtain ⟨k, hk1, hk2, rfl⟩ := (mem_seg x).1 hvs
    rcases hmem _ (List.mem_reverse.1 hv) with ⟨k', hk', he⟩ | he | ⟨hoff, -⟩
    · have := hinj _ _ (by omega) (by omega) he
      have : k = u := by omega
      rw [this]
    · have := hinj _ _ (by omega) (by omega) he; omega
    · exact absurd ⟨k, by omega, rfl⟩ hoff
  have hnd2 : (L.reverse ++ (seg x u s).tail ++ Q.tail).Nodup := by
    refine nodup_append_tail hnd1 hQnd hQPL ?_
    intro v hv hvQ
    rcases hQmem v hvQ with he | he | hoff
    · exact he
    · exfalso
      subst he
      rcases mem_append_tail hv with hv | hv
      · rcases hmem _ (List.mem_reverse.1 hv) with ⟨k', hk', he⟩ | he | ⟨hoff, -⟩
        · have := hinj _ _ (by omega) (by omega) he; omega
        · have := hinj _ _ (by omega) (by omega) he; omega
        · exact hoff ⟨t, htm, rfl⟩
      · obtain ⟨k, hk1, hk2, he⟩ := (mem_seg x).1 hv
        have := hinj _ _ (by omega) (by omega) he; omega
    · exfalso
      rcases mem_append_tail hv with hv | hv
      · rcases hmem _ (List.mem_reverse.1 hv) with ⟨k', hk', he⟩ | he | ⟨-, p, hp, hat⟩
        · exact hoff ⟨k', by omega, he⟩
        · exact hoff ⟨w, hwm, he.symm⟩
        · have := hRB p t hp (br_of_AT x m hat (hQat v hvQ hoff).2 (by omega) htm)
          omega
      · obtain ⟨k, hk1, hk2, he⟩ := (mem_seg x).1 hv
        exact hoff ⟨k, by omega, he⟩
  refine ⟨t, _, hwt, hwt, htm, hk, hmax, D, hnd2, ?_, ?_⟩
  · intro v hv
    rcases mem_append_tail hv with hv | hvQ
    · rcases mem_append_tail hv with hv | hv
      · rcases hmem _ (List.mem_reverse.1 hv) with ⟨k', hk', he⟩ | he | ⟨hoff, p, hp, hat⟩
        · exact Or.inl ⟨k', by omega, he⟩
        · exact Or.inl ⟨w, le_rfl, he.symm⟩
        · exact Or.inr (Or.inr ⟨hoff, p, by omega, hat⟩)
      · obtain ⟨k, hk1, hk2, he⟩ := (mem_seg x).1 hv
        exact Or.inl ⟨k, by omega, he⟩
    · rcases hQmem v hvQ with he | he | hoff
      · exact Or.inl ⟨s, by omega, he.symm⟩
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr ⟨hoff, s, hsw, (hQat v hvQ hoff).1⟩)
  · have hl1 := length_append_tail (L := L.reverse) P2.length_pos
    have hl2 := length_append_tail (L := L.reverse ++ (seg x u s).tail) hQPL.length_pos
    rw [List.length_reverse, length_seg] at hl1
    have := hQPL.length_pos
    omega

lemma chain_base (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1)))
    (hconn : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support)
    {S T : Finset ℕ} (hS : ∀ k ∈ S, k < m ∧ G.Adj (x 0) (x (k+1)))
    (hT : ∀ k ∈ T, k < m ∧ G.Adj (x k) (x m))
    (hsep : ∀ i ∈ S, ∀ j ∈ T, i < j) (hSne : S.Nonempty) (hTne : T.Nonempty) :
    ∃ u w L, Inv x m G S T u w L := by
  classical
  set a' := S.max' hSne with ha'def
  have ha'S : a' ∈ S := Finset.max'_mem _ _
  have ha'max : ∀ k ∈ S, k ≤ a' := fun k hk => Finset.le_max' _ k hk
  obtain ⟨j0, hj0⟩ := hTne
  have h1 := hsep a' ha'S j0 hj0
  have h2 := (hT j0 hj0).1
  obtain ⟨s, t, hsa, hat, hb, hmax⟩ :=
    max_bridge x m hinj hconn (by omega : 0 < a' + 1) (by omega : a' + 1 < m)
  have htm : t ≤ m := hb.2.1
  obtain ⟨Q, hQPL, hQnd, hQmem, hQat⟩ := path_of_br x m hb
  have hne : (S.filter (fun k => s ≤ k)).Nonempty := ⟨a', Finset.mem_filter.2 ⟨ha'S, by omega⟩⟩
  set i' := (S.filter (fun k => s ≤ k)).min' hne with hi'def
  have hi'S : i' ∈ S ∧ s ≤ i' := Finset.mem_filter.1 (Finset.min'_mem _ _)
  have hi'min : ∀ k ∈ S, s ≤ k → i' ≤ k := fun k hk hsk =>
    Finset.min'_le _ k (Finset.mem_filter.2 ⟨hk, hsk⟩)
  have hi'a : i' ≤ a' := ha'max i' hi'S.1
  have P1 : PL G (x (a'+1)) (seg x (i'+1) (a'+1)).reverse (x (i'+1)) :=
    (PL_seg x m hadj (by omega) (by omega)).reverse
  have P2 : PL G (x (i'+1)) [x (i'+1), x 0] (x 0) := PL.edge (hS i' hi'S.1).2.symm
  have P3 : PL G (x 0) (seg x 0 s) (x s) := PL_seg x m hadj (Nat.zero_le _) (by omega)
  have E1 := P1.append P2
  have E2 := E1.append P3
  have E := E2.append hQPL
  have hx0 : ∀ k, k ≤ m → x k = x 0 → k = 0 := fun k hk he => hinj _ _ hk (by omega) he
  have hnd1 : ((seg x (i'+1) (a'+1)).reverse ++ [x (i'+1), x 0].tail).Nodup := by
    refine nodup_append_tail (List.nodup_reverse.2 (nodup_seg x m hinj (by omega))) ?_ P2 ?_
    · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_true]
      intro he; have := hx0 _ (by omega) he; omega
    · intro v hv hv2
      obtain ⟨k, hk1, hk2, rfl⟩ := (mem_seg x).1 (List.mem_reverse.1 hv)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv2
      rcases hv2 with he | he
      · exact he
      · have := hx0 _ (by omega) he; omega
  have hmem1 : ∀ v ∈ (seg x (i'+1) (a'+1)).reverse ++ [x (i'+1), x 0].tail,
      v = x 0 ∨ ∃ k, i' + 1 ≤ k ∧ k ≤ a' + 1 ∧ x k = v := by
    intro v hv
    rcases mem_append_tail hv with hv | hv
    · exact Or.inr ((mem_seg x).1 (List.mem_reverse.1 hv))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact Or.inr ⟨i'+1, le_rfl, by omega, rfl⟩
      · exact Or.inl rfl
  have hnd2 : ((seg x (i'+1) (a'+1)).reverse ++ [x (i'+1), x 0].tail ++
      (seg x 0 s).tail).Nodup := by
    refine nodup_append_tail hnd1 (nodup_seg x m hinj (by omega)) P3 ?_
    intro v hv hvs
    obtain ⟨k, hk1, hk2, rfl⟩ := (mem_seg x).1 hvs
    rcases hmem1 _ hv with he | ⟨k', hk1', hk2', he⟩
    · exact he
    · have := hinj _ _ (by omega) (by omega) he; omega
  have hmem2 : ∀ v ∈ (seg x (i'+1) (a'+1)).reverse ++ [x (i'+1), x 0].tail ++
      (seg x 0 s).tail, ∃ k, k ≤ a' + 1 ∧ x k = v := by
    intro v hv
    rcases mem_append_tail hv with hv | hv
    · rcases hmem1 _ hv with he | ⟨k', hk1', hk2', he⟩
      · exact ⟨0, by omega, he.symm⟩
      · exact ⟨k', hk2', he⟩
    · obtain ⟨k, hk1, hk2, he⟩ := (mem_seg x).1 hv
      exact ⟨k, by omega, he⟩
  have hnd3 : ((seg x (i'+1) (a'+1)).reverse ++ [x (i'+1), x 0].tail ++
      (seg x 0 s).tail ++ Q.tail).Nodup := by
    refine nodup_append_tail hnd2 hQnd hQPL ?_
    intro v hv hvQ
    obtain ⟨k, hk, rfl⟩ := hmem2 v hv
    rcases hQmem _ hvQ with he | he | hoff
    · exact he
    · have := hinj _ _ (by omega) htm he; omega
    · exact absurd ⟨k, by omega, rfl⟩ hoff
  refine ⟨a' + 1, t, _, hat, htm, fun k hk => hsep a' ha'S k hk, hmax, E, hnd3, ?_, ?_⟩
  · intro v hv
    rcases mem_append_tail hv with hv | hvQ
    · exact Or.inl (hmem2 v hv)
    · rcases hQmem v hvQ with he | he | hoff
      · exact Or.inl ⟨s, by omega, he.symm⟩
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr ⟨hoff, s, hsa, (hQat v hvQ hoff).1⟩)
  · have hSsub : S ⊆ Finset.range s ∪ Finset.Icc i' a' := by
      intro k hk
      rw [Finset.mem_union, Finset.mem_range, Finset.mem_Icc]
      rcases Nat.lt_or_ge k s with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hi'min k hk h, ha'max k hk⟩
    have hSc := (Finset.card_le_card hSsub).trans (Finset.card_union_le _ _)
    rw [Finset.card_range, Nat.card_Icc] at hSc
    have hl1 := length_append_tail (L := (seg x (i'+1) (a'+1)).reverse) P2.length_pos
    have hl2 := length_append_tail
      (L := (seg x (i'+1) (a'+1)).reverse ++ [x (i'+1), x 0].tail) P3.length_pos
    have hl3 := length_append_tail
      (L := (seg x (i'+1) (a'+1)).reverse ++ [x (i'+1), x 0].tail ++ (seg x 0 s).tail)
      hQPL.length_pos
    rw [List.length_reverse, length_seg] at hl1
    rw [length_seg] at hl2
    simp only [List.length_cons, List.length_nil] at hl1
    have := hQPL.length_pos
    omega

lemma chain_iter (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1)))
    (hconn : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support)
    {S T : Finset ℕ} (hT : ∀ k ∈ T, k < m ∧ G.Adj (x k) (x m))
    (h3 : 3 ≤ S.card + T.card) (hTne : T.Nonempty) :
    ∀ N u w L, m - w = N → Inv x m G S T u w L →
      ∃ (y : V) (c : G.Walk y y), c.IsCycle ∧ S.card + T.card ≤ c.length := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro u w L hN hI
    by_cases hk : ∃ k ∈ T, k < w
    · exact close_cycle x m hinj hadj hT hI hk h3
    · push Not at hk
      obtain ⟨t, L', hwt, hI'⟩ := chain_step x m hinj hadj hconn hT hI hk hTne
      have htm : t ≤ m := hI'.2.1
      exact ih (m - t) (by omega) w t L' rfl hI'


/-! Case of a neighbour of `x m` preceding a neighbour of `x 0`, and the combined lemma. -/

lemma case_two (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1)))
    {S T : Finset ℕ} (hS : ∀ k ∈ S, k < m ∧ G.Adj (x 0) (x (k+1)))
    (hT : ∀ k ∈ T, k < m ∧ G.Adj (x k) (x m)) (hdisj : ∀ k ∈ S, k ∉ T)
    (h : ∃ j ∈ T, ∃ i ∈ S, j < i) (h3 : 3 ≤ S.card + T.card) :
    ∃ (y : V) (c : G.Walk y y), c.IsCycle ∧ S.card + T.card ≤ c.length := by
  classical
  obtain ⟨j0, hj0T, i0, hi0S, hji⟩ := h
  have hne : (S.filter (fun k => j0 < k)).Nonempty := ⟨i0, Finset.mem_filter.2 ⟨hi0S, hji⟩⟩
  set i1 := (S.filter (fun k => j0 < k)).min' hne with hi1def
  have hi1 : i1 ∈ S ∧ j0 < i1 := Finset.mem_filter.1 (Finset.min'_mem _ _)
  have hi1min : ∀ k ∈ S, j0 < k → i1 ≤ k := fun k hk h =>
    Finset.min'_le _ k (Finset.mem_filter.2 ⟨hk, h⟩)
  have hne2 : (T.filter (fun k => k < i1)).Nonempty := ⟨j0, Finset.mem_filter.2 ⟨hj0T, hi1.2⟩⟩
  set j1 := (T.filter (fun k => k < i1)).max' hne2 with hj1def
  have hj1 : j1 ∈ T ∧ j1 < i1 := Finset.mem_filter.1 (Finset.max'_mem _ _)
  have hj1max : ∀ k ∈ T, k < i1 → k ≤ j1 := fun k hk h =>
    Finset.le_max' _ k (Finset.mem_filter.2 ⟨hk, h⟩)
  have hj0j1 : j0 ≤ j1 := hj1max j0 hj0T hi1.2
  have hi1m := (hS i1 hi1.1).1
  have P1 : PL G (x 0) (seg x 0 j1) (x j1) := PL_seg x m hadj (Nat.zero_le _) (by omega)
  have P2 : PL G (x j1) [x j1, x m] (x m) := PL.edge (hT j1 hj1.1).2
  have P3 : PL G (x m) (seg x (i1+1) m).reverse (x (i1+1)) :=
    (PL_seg x m hadj (by omega) le_rfl).reverse
  have F := (P1.append P2).append P3
  have hnd1 : (seg x 0 j1 ++ [x j1, x m].tail).Nodup := by
    refine nodup_append_tail (nodup_seg x m hinj (by omega)) ?_ P2 ?_
    · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_true]
      intro he; have := hinj _ _ (by omega) le_rfl he; omega
    · intro v hv hv2
      obtain ⟨k, hk1, hk2, rfl⟩ := (mem_seg x).1 hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv2
      rcases hv2 with he | he
      · exact he
      · have := hinj _ _ (by omega) le_rfl he; omega
  have hnd2 : (seg x 0 j1 ++ [x j1, x m].tail ++ (seg x (i1+1) m).reverse.tail).Nodup := by
    refine nodup_append_tail hnd1 (List.nodup_reverse.2 (nodup_seg x m hinj le_rfl)) P3 ?_
    intro v hv hvs
    obtain ⟨k, hk1, hk2, rfl⟩ := (mem_seg x).1 (List.mem_reverse.1 hvs)
    rcases mem_append_tail hv with hv | hv
    · obtain ⟨k', hk1', hk2', he⟩ := (mem_seg x).1 hv
      have := hinj _ _ (by omega) (by omega) he; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with he | he
      · have := hinj _ _ (by omega) (by omega) he; omega
      · exact he
  have hsub : S ∪ T ⊆ Finset.range (j1 + 1) ∪ Finset.Ico i1 m := by
    intro k hk
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    rcases Finset.mem_union.1 hk with hk | hk
    · have := (hS k hk).1
      rcases Nat.lt_or_ge j1 k with h | h
      · have := hi1min k hk (by omega); right; omega
      · left; omega
    · have := (hT k hk).1
      rcases Nat.lt_or_ge k i1 with h | h
      · have := hj1max k hk h; left; omega
      · right; omega
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_left.2 hdisj), Finset.card_range,
    Nat.card_Ico] at hc
  have hl1 := length_append_tail (L := seg x 0 j1) P2.length_pos
  have hl2 := length_append_tail (L := seg x 0 j1 ++ [x j1, x m].tail) P3.length_pos
  rw [length_seg] at hl1
  rw [List.length_reverse, length_seg] at hl2
  simp only [List.length_cons, List.length_nil] at hl1
  obtain ⟨y, c, hcyc, hcl⟩ := cycle_of_PL F (hS i1 hi1.1).2.symm hnd2 (by omega)
  exact ⟨y, c, hcyc, by omega⟩

/-- Bondy-type lemma: a path `x 0, ..., x m` in a 2-connected graph, with no crossing pair of
end chords, yields a cycle of length at least `|S| + |T|`. -/
lemma long_cycle (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1)))
    (hconn : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support)
    {S T : Finset ℕ} (hS : ∀ k ∈ S, k < m ∧ G.Adj (x 0) (x (k+1)))
    (hT : ∀ k ∈ T, k < m ∧ G.Adj (x k) (x m)) (hdisj : ∀ k ∈ S, k ∉ T)
    (hS1 : 1 ≤ S.card) (hT1 : 1 ≤ T.card) (h3 : 3 ≤ S.card + T.card) :
    ∃ (y : V) (c : G.Walk y y), c.IsCycle ∧ S.card + T.card ≤ c.length := by
  by_cases h : ∃ j ∈ T, ∃ i ∈ S, j < i
  · exact case_two x m hinj hadj hS hT hdisj h h3
  · have hsep : ∀ i ∈ S, ∀ j ∈ T, i < j := by
      intro i hi j hj
      rcases Nat.lt_trichotomy i j with h' | h' | h'
      · exact h'
      · subst h'; exact absurd hj (hdisj i hi)
      · exact absurd ⟨j, hj, i, hi, h'⟩ h
    have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
    have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨u, w, L, hI⟩ := chain_base x m hinj hadj hconn hS hT hsep hSne hTne
    exact chain_iter x m hinj hadj hconn hT h3 hTne _ u w L rfl hI


/-! Longest paths (adapted from philipsaint's proof of Dirac's Hamiltonicity theorem). -/

def Cyc (G : SimpleGraph V) (c : List V) : Prop :=
  c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b

lemma rot {c : List V} (hc : Cyc G c) {q : V} (hq : q ∈ c) :
    ∃ c' : List V, c'.Perm c ∧ c'.IsChain G.Adj ∧ c'.head? = some q := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hq
  refine ⟨(q :: B) ++ A, List.perm_append_comm, ?_, by simp⟩
  obtain ⟨hch, hcl⟩ := hc
  rw [List.isChain_append] at hch
  refine List.isChain_append.2 ⟨hch.2.1, hch.1, ?_⟩
  intro x hx y hy
  apply hcl
  · rw [List.getLast?_append]
    have : (q :: B).getLast? = some x := hx
    simp [this]
  · rw [List.head?_append, hy]
    rfl

lemma getD_zero (l : List V) (hl : l ≠ []) (d : V) : l.getD 0 d = l.head hl := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => rfl

lemma getD_last (l : List V) (hl : l ≠ []) (d : V) : l.getD (l.length - 1) d = l.getLast hl := by
  rw [List.getLast_eq_getElem, List.getD_eq_getElem]

theorem dirac_core [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (d : ℕ) (hd : 2 ≤ d)
    (h3 : 3 ≤ Fintype.card V)
    (hconn : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support)
    (hreach : ∀ a b : V, G.Reachable a b) (hdeg : ∀ v, d ≤ G.degree v) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ min (Fintype.card V) (2 * d) ≤ c.length := by
  classical
  set n := Fintype.card V with hn
  obtain ⟨v0⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let PP : ℕ → Prop := fun k => ∃ l : List V, (l.Nodup ∧ l.IsChain G.Adj) ∧ l.length = k
  have h1 : PP 1 := ⟨[v0], ⟨by simp, List.isChain_singleton _⟩, rfl⟩
  set M := Nat.findGreatest PP n
  obtain ⟨l, ⟨hlnd, hlch⟩, hlM⟩ : PP M := Nat.findGreatest_spec (by omega) h1
  have hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ M :=
    fun l' h1 h2 => Nat.le_findGreatest h1.length_le_card ⟨l', ⟨h1, h2⟩, rfl⟩
  have hM1 : 1 ≤ M := Nat.le_findGreatest (by omega) h1
  have hl_ne : l ≠ [] := by
    rintro rfl
    simp at hlM
    omega
  set q0 := l.head hl_ne
  set z := l.getLast hl_ne
  have hmn : l.length ≤ n := hlnd.length_le_card
  have ext_head : ∀ y, G.Adj q0 y → y ∈ l := by
    intro y hy
    by_contra hyl
    have := hmax (y :: l) (List.nodup_cons.2 ⟨hyl, hlnd⟩)
      (List.IsChain.cons_of_ne_nil hl_ne hlch ((hy).symm))
    simp at this
    omega
  have ext_last : ∀ y, G.Adj z y → y ∈ l := by
    intro y hy
    by_contra hyl
    have hch : (l ++ [y]).IsChain G.Adj := by
      refine List.isChain_append.2 ⟨hlch, List.isChain_singleton _, ?_⟩
      intro x hx y' hy'
      rw [List.getLast?_eq_some_getLast hl_ne] at hx
      simp at hx hy'
      subst hx hy'
      exact hy
    have hnd : (l ++ [y]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hlnd, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp at hb
      subst hb
      rintro rfl
      exact hyl ha
    have := hmax _ hnd hch
    simp at this
    omega
  set m := l.length with hm
  have hq0 : l.getD 0 q0 = q0 := getD_zero l hl_ne q0
  have hz : l.getD (m - 1) q0 = z := getD_last l hl_ne q0
  let S := (Finset.range (m - 1)).filter (fun j => G.Adj q0 (l.getD (j + 1) q0))
  let T := (Finset.range (m - 1)).filter (fun j => G.Adj (l.getD j q0) z)
  have hS : G.degree q0 ≤ S.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := S)
      (f := fun j => l.getD (j + 1) q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_head y hy)
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hq0]
    rw [Finset.mem_image]
    refine ⟨k - 1, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
      exact hy
    · rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
  have hT : G.degree z ≤ T.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := T)
      (f := fun j => l.getD j q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_last y hy)
    have hkm : k ≠ m - 1 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hz]
    rw [Finset.mem_image]
    refine ⟨k, ?_, List.getD_eq_getElem _ _ hk⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [List.getD_eq_getElem _ _ hk]
    exact (hy).symm
  have hdq := hdeg q0
  have hdz := hdeg z
  by_cases hcross : ∃ j, j ∈ S ∧ j ∈ T
  · obtain ⟨j, hjS, hjT⟩ := hcross
    rw [Finset.mem_filter, Finset.mem_range] at hjS hjT
    obtain ⟨hjm, hA⟩ := hjS
    obtain ⟨-, hB⟩ := hjT
    set c := l.take (j + 1) ++ (l.drop (j + 1)).reverse with hcdef
    have hperm : c.Perm l := by
      have := (List.Perm.append_left (l.take (j + 1)) (List.reverse_perm (l.drop (j + 1))))
      rw [List.take_append_drop] at this
      exact this
    have hcnd : c.Nodup := hperm.nodup_iff.mpr hlnd
    have hj1 : j < m := by omega
    have hj2 : j + 1 < m := by omega
    have e1 : (l.take (j + 1)).getLast? = some (l.getD j q0) := by
      rw [List.getLast?_take, List.getD_eq_getElem _ _ hj1]
      simp [List.getElem?_eq_getElem hj1]
    have e2 : (l.drop (j + 1)).reverse.head? = some z := by
      rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega),
        List.getLast?_eq_some_getLast hl_ne]
    have e3 : c.getLast? = some (l.getD (j + 1) q0) := by
      rw [hcdef, List.getLast?_append, List.getLast?_reverse, List.head?_drop,
        List.getElem?_eq_getElem hj2, List.getD_eq_getElem _ _ hj2]
      rfl
    have e4 : c.head? = some q0 := by
      rw [hcdef, List.head?_append, List.head?_take]
      simp [List.head?_eq_some_head hl_ne, q0]
    have hchain : c.IsChain G.Adj := by
      refine List.isChain_append.2 ⟨hlch.take _, ?_, ?_⟩
      · rw [List.isChain_reverse]
        exact (hlch.drop _).imp (fun a b h => h.symm)
      · intro x hx y hy
        rw [e1] at hx
        rw [e2] at hy
        simp at hx hy
        subst hx hy
        exact hB
    have hcyc : Cyc G c := by
      refine ⟨hchain, ?_⟩
      intro a ha b hb
      rw [e3] at ha
      rw [e4] at hb
      simp at ha hb
      subst ha hb
      exact (hA).symm
    have hall : ∀ w, w ∈ l := by
      intro w
      by_contra hw
      obtain ⟨p⟩ := hreach q0 w
      obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {x | x ∈ l} (List.head_mem hl_ne) hw
      have hqc : d.fst ∈ c := hperm.mem_iff.mpr hd1
      obtain ⟨c', hc'p, hc'ch, hc'h⟩ := rot hcyc hqc
      have hnd' : (d.snd :: c').Nodup := by
        refine List.nodup_cons.2 ⟨?_, (hc'p.trans hperm).nodup_iff.mpr hlnd⟩
        intro hmem
        exact hd2 ((hc'p.trans hperm).mem_iff.mp hmem)
      have hch' : (d.snd :: c').IsChain G.Adj := by
        refine List.isChain_cons.2 ⟨?_, hc'ch⟩
        intro y hy
        rw [hc'h] at hy
        simp at hy
        subst hy
        exact (d.adj).symm
      have := hmax _ hnd' hch'
      rw [List.length_cons, (hc'p.trans hperm).length_eq] at this
      omega
    have hmn' : m = n := by
      have h1 : l.toFinset = Finset.univ := by
        ext w
        simp [hall w]
      have h2 := List.toFinset_card_of_nodup hlnd
      rw [h1, Finset.card_univ] at h2
      omega
    have hclen : c.length = n := by rw [hperm.length_eq]; exact hmn'
    obtain ⟨y, w, hw, hwl⟩ := cycle_of_PL (G := G) ⟨hchain, e4, e3⟩ hA.symm hcnd (by omega)
    exact ⟨y, w, hw, by rw [hwl, hclen]; exact min_le_left _ _⟩
  · push Not at hcross
    let x : ℕ → V := fun k => l.getD k q0
    have hinj : ∀ i j, i ≤ m - 1 → j ≤ m - 1 → x i = x j → i = j := by
      intro i j hi hj he
      simp only [x] at he
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at he
      exact (hlnd.getElem_inj_iff).1 he
    have hadj : ∀ i, i < m - 1 → G.Adj (x i) (x (i+1)) := by
      intro i hi
      simp only [x]
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      exact List.isChain_iff_getElem.1 hlch i (by omega)
    have hx0 : x 0 = q0 := hq0
    have hxm : x (m - 1) = z := hz
    have hS' : ∀ k ∈ S, k < m - 1 ∧ G.Adj (x 0) (x (k+1)) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      exact ⟨hk.1, by rw [hx0]; exact hk.2⟩
    have hT' : ∀ k ∈ T, k < m - 1 ∧ G.Adj (x k) (x (m - 1)) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      exact ⟨hk.1, by rw [hxm]; exact hk.2⟩
    obtain ⟨y, w, hw, hwl⟩ := long_cycle x (m - 1) hinj hadj hconn hS' hT'
      (fun k hk hkT => hcross k hk hkT) (by omega) (by omega) (by omega)
    exact ⟨y, w, hw, le_trans (min_le_right _ _) (by omega)⟩

end C1

theorem core : CoreStatement := by
  intro V _ _ G _ d hd h3 hG hconn hdeg
  exact C1.dirac_core d hd h3 hconn (fun a b => hG.preconnected a b) hdeg

end OMA.EG


namespace OMA.EG
open SimpleGraph Finset

/-- The target step H1 (copied verbatim from reductions/opg-forcing-a-2-regular-minor.R1.lean). -/
def H1Statement : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
    3 ≤ k → (k - 1) * Fintype.card V ≤ 2 * G.edgeFinset.card →
      ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length

lemma lift_cycle {V : Type} (G : SimpleGraph V) (S : Set V) {k : ℕ}
    (h : ∃ (u : S) (c : (G.induce S).Walk u u), c.IsCycle ∧ k ≤ c.length) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length := by
  obtain ⟨u, c, hc, hk⟩ := h
  refine ⟨_, c.map (Embedding.induce (G := G) S).toHom, ?_, ?_⟩
  · exact (Walk.isCycle_map_iff_of_injective (Embedding.induce (G := G) S).injective).2 hc
  · rw [Walk.length_map]; exact hk

lemma edges_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) [Fintype (G.induce (s : Set V)).edgeSet] :
    #(G.edgeFinset ∩ s.sym2) ≤ #(G.induce (s : Set V)).edgeFinset := by
  let f : Sym2 (s : Set V) ↪ Sym2 V :=
    ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩
  rw [← Finset.card_map f]
  apply Finset.card_le_card
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    rw [Finset.mem_inter, mem_edgeFinset, mem_edgeSet, Finset.mem_sym2_iff] at he
    obtain ⟨hxy, hs⟩ := he
    have hx : x ∈ (s : Set V) := hs x (Sym2.mem_mk_left x y)
    have hy : y ∈ (s : Set V) := hs y (Sym2.mem_mk_right x y)
    rw [Finset.mem_map]
    refine ⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_, ?_⟩
    · rw [mem_edgeFinset, mem_edgeSet]; exact hxy
    · rfl

lemma card_sub {V : Type} [Fintype V] (s : Finset V) [Fintype (s : Set V)] :
    Fintype.card (s : Set V) = #s := by simp

def EGP (n : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
    Fintype.card V = n → 3 ≤ k → (k - 1) * (n - 1) < 2 * #G.edgeFinset →
      ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length

lemma apply_sub {n : ℕ} (ih : ∀ m < n, EGP m) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k) (s : Finset V) (hs : #s < n)
    (he : (k - 1) * (#s - 1) < 2 * #(G.edgeFinset ∩ s.sym2)) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length := by
  classical
  apply lift_cycle G (s : Set V)
  apply ih #s hs (s : Set V) (G.induce (s : Set V)) k (card_sub s) hk
  have := edges_le G s
  omega

lemma sep_case {n : ℕ} (ih : ∀ m < n, EGP m) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k) (hn : Fintype.card V = n)
    (he : (k - 1) * (n - 1) < 2 * #G.edgeFinset) (V1 V2 : Finset V) (hU : V1 ∪ V2 = univ)
    (hI : #(V1 ∩ V2) ≤ 1) (h1 : #V1 < n) (h2 : #V2 < n)
    (hE : ∀ x y, G.Adj x y → (x ∈ V1 ∧ y ∈ V1) ∨ (x ∈ V2 ∧ y ∈ V2)) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length := by
  have hsub : G.edgeFinset ⊆ (G.edgeFinset ∩ V1.sym2) ∪ (G.edgeFinset ∩ V2.sym2) := by
    intro e he'
    induction e using Sym2.ind with
    | h x y =>
      have hxy : G.Adj x y := by rwa [mem_edgeFinset, mem_edgeSet] at he'
      rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter, Finset.mem_sym2_iff,
        Finset.mem_sym2_iff]
      rcases hE x y hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · left
        refine ⟨he', fun a ha => ?_⟩
        rcases Sym2.mem_iff.1 ha with rfl | rfl <;> assumption
      · right
        refine ⟨he', fun a ha => ?_⟩
        rcases Sym2.mem_iff.1 ha with rfl | rfl <;> assumption
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hUI := Finset.card_union_add_card_inter V1 V2
  rw [hU, Finset.card_univ, hn] at hUI
  by_cases c1 : (k - 1) * (#V1 - 1) < 2 * #(G.edgeFinset ∩ V1.sym2)
  · exact apply_sub ih G hk V1 h1 c1
  by_cases c2 : (k - 1) * (#V2 - 1) < 2 * #(G.edgeFinset ∩ V2.sym2)
  · exact apply_sub ih G hk V2 h2 c2
  exfalso
  have h3 : (#V1 - 1) + (#V2 - 1) ≤ n - 1 := by omega
  have h4 := Nat.mul_le_mul_left (k - 1) h3
  rw [Nat.mul_add] at h4
  omega

lemma del_case {n : ℕ} (ih : ∀ m < n, EGP m) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k) (hn : Fintype.card V = n)
    (hkn : k ≤ n) (he : (k - 1) * (n - 1) < 2 * #G.edgeFinset) (v : V)
    (hv : 2 * G.degree v ≤ k - 1) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length := by
  have hsub : G.edgeFinset ⊆ (G.edgeFinset ∩ (univ.erase v).sym2) ∪ G.incidenceFinset v := by
    intro e he'
    rw [Finset.mem_union, Finset.mem_inter, Finset.mem_sym2_iff, mem_incidenceFinset]
    by_cases hve : v ∈ e
    · right
      exact ⟨by rwa [mem_edgeFinset] at he', hve⟩
    · left
      refine ⟨he', fun a ha => ?_⟩
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ a⟩
      rintro rfl
      exact hve ha
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [card_incidenceFinset_eq_degree] at hc
  have hs : #(univ.erase v) = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hn]
  apply apply_sub ih G hk (univ.erase v) (by omega)
  rw [hs]
  have h5 : (k - 1) * (n - 1) = (k - 1) * (n - 1 - 1) + (k - 1) := by
    conv_lhs => rw [show n - 1 = (n - 1 - 1) + 1 by omega]
    rw [Nat.mul_add, Nat.mul_one]
  omega

lemma cut_sep {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v a b : V)
    (ha : a ≠ v) (hb : b ≠ v) (hcut : ∀ p : G.Walk a b, v ∈ p.support) :
    ∃ V1 V2 : Finset V, V1 ∪ V2 = univ ∧ #(V1 ∩ V2) ≤ 1 ∧ #V1 < Fintype.card V ∧
      #V2 < Fintype.card V ∧ ∀ x y, G.Adj x y → (x ∈ V1 ∧ y ∈ V1) ∨ (x ∈ V2 ∧ y ∈ V2) := by
  classical
  obtain ⟨R, hR⟩ : ∃ R : Finset V, ∀ w, w ∈ R ↔ ∃ p : G.Walk a w, v ∉ p.support :=
    ⟨univ.filter (fun w => ∃ p : G.Walk a w, v ∉ p.support), fun w => by simp⟩
  have hext : ∀ x y, G.Adj x y → x ∈ R → y ≠ v → y ∈ R := by
    intro x y hxy hx hy
    obtain ⟨p, hp⟩ := (hR x).1 hx
    refine (hR y).2 ⟨p.concat hxy, ?_⟩
    rw [Walk.support_concat, List.mem_append, List.mem_singleton]
    rintro (h | h)
    · exact hp h
    · exact hy h.symm
  refine ⟨insert v R, univ \ R, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.eq_univ_iff_forall.2
    intro x
    by_cases hx : x ∈ R
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hx)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨Finset.mem_univ x, hx⟩)
  · have : insert v R ∩ (univ \ R) ⊆ {v} := by
      intro x hx
      rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_sdiff] at hx
      rw [Finset.mem_singleton]
      rcases hx with ⟨h | h, -, h'⟩
      · exact h
      · exact absurd h h'
    exact (Finset.card_le_card this).trans (Finset.card_singleton v).le
  · apply Finset.card_lt_univ_of_notMem (x := b)
    rw [Finset.mem_insert, not_or]
    refine ⟨hb, fun h => ?_⟩
    obtain ⟨p, hp⟩ := (hR b).1 h
    exact hp (hcut p)
  · apply Finset.card_lt_univ_of_notMem (x := a)
    rw [Finset.mem_sdiff, not_and, not_not]
    intro _
    refine (hR a).2 ⟨Walk.nil, ?_⟩
    rw [Walk.support_nil, List.mem_singleton]
    exact fun h => ha h.symm
  · intro x y hxy
    by_cases hx : x ∈ R
    · left
      refine ⟨Finset.mem_insert_of_mem hx, ?_⟩
      by_cases hyv : y = v
      · rw [hyv]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hext x y hxy hx hyv)
    · by_cases hy : y ∈ R
      · left
        refine ⟨?_, Finset.mem_insert_of_mem hy⟩
        by_cases hxv : x = v
        · rw [hxv]; exact Finset.mem_insert_self _ _
        · exact absurd (hext y x hxy.symm hy hxv) hx
      · right
        exact ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ x, hx⟩,
          Finset.mem_sdiff.2 ⟨Finset.mem_univ y, hy⟩⟩

lemma conn_of {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (h3 : 3 ≤ Fintype.card V)
    (h2c : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support) : G.Connected := by
  have hne : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  refine { preconnected := fun a b => ?_, nonempty := hne }
  by_cases hab : a = b
  · rw [hab]
  · have hcard : 1 < #(univ.erase a) := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
      omega
    obtain ⟨v, hv, hvb⟩ := Finset.exists_mem_ne hcard b
    obtain ⟨p, -⟩ := h2c v a b (Finset.ne_of_mem_erase hv).symm hvb.symm
    exact ⟨p⟩

lemma two_e_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * #G.edgeFinset ≤ Fintype.card V * (Fintype.card V - 1) := by
  have h := G.card_edgeFinset_le_card_choose_two
  rw [Nat.choose_two_right] at h
  have := Nat.mul_div_le (Fintype.card V * (Fintype.card V - 1)) 2
  omega

theorem main_ind (core : CoreStatement) (n : ℕ) : EGP n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ G _ k hn hk he
  have hkn : k ≤ n := by
    have h := two_e_le G
    rw [hn] at h
    have h' : (k - 1) * (n - 1) < n * (n - 1) := lt_of_lt_of_le he h
    have := Nat.lt_of_mul_lt_mul_right h'
    omega
  by_cases hA : ∃ v, 2 * G.degree v ≤ k - 1
  · obtain ⟨v, hv⟩ := hA
    exact del_case ih G hk hn hkn he v hv
  push Not at hA
  by_cases h2c : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support
  · have h3 : 3 ≤ Fintype.card V := by omega
    obtain ⟨u, c, hc, hlen⟩ := core G ((k + 1) / 2) (by omega) h3 (conn_of G h3 h2c) h2c
      (fun v => by have := hA v; omega)
    refine ⟨u, c, hc, le_trans ?_ hlen⟩
    rw [hn]
    exact Nat.le_min.2 ⟨hkn, by omega⟩
  · push Not at h2c
    obtain ⟨v, a, b, ha, hb, hcut⟩ := h2c
    obtain ⟨V1, V2, hU, hI, h1, h2, hE⟩ := cut_sep G v a b ha hb hcut
    rw [hn] at h1 h2
    exact sep_case ih G hk hn he V1 V2 hU hI h1 h2 hE

theorem frame : CoreStatement → H1Statement := by
  intro core V _ _ G _ k hk he
  classical
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  apply main_ind core (Fintype.card V) V G k rfl hk
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 1 := ⟨Fintype.card V - 1, by omega⟩
  rw [hm] at he ⊢
  rw [Nat.add_sub_cancel]
  rw [Nat.mul_add, Nat.mul_one] at he
  convert (show (k - 1) * m < 2 * #G.edgeFinset by omega) using 4

end OMA.EG


theorem OMA.solution : OMA.R_opg_forcing_a_2_regular_minor_R1.H1 :=
  OMA.EG.frame OMA.EG.core
