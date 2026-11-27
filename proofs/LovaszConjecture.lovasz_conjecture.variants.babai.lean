import FormalConjectures.Wikipedia.LovaszConjecture

/-!
# Babai's Theorem (1979): Long Cycles in Vertex-Transitive Graphs

Every finite connected vertex-transitive graph on $n \ge 3$ vertices contains a cycle of length
at least $\sqrt{3n}$.

## Proof Outline
1. **Regularity & $d \ge 2$:** By vertex-transitivity, $G$ is $d$-regular. Since $G$ is connected
   and $n \ge 3$, $d \ge 2$.
2. **Case $d = 2$:** A connected $2$-regular finite graph is a single cycle of length $n \ge 3$,
   and $n \ge \sqrt{3n}$.
3. **Watkins' 3-Connectivity Theorem ($d \ge 3$):** Every connected vertex-transitive graph of
   degree $d \ge 3$ is $3$-connected (no separating set of size $\le 2$), proved via atomic parts
   and triangle-count symmetry for the $d = 3, a = \kappa = 2$ boundary case.
4. **2-Path Menger Lemma:** In a $2$-connected graph, between any two disjoint subsets $A, B$ of
   size $\ge 2$, there exist two vertex-disjoint paths from $A$ to $B$ (proved via 1-step
   augmenting path on a vertex-split residual graph).
5. **Longest-Cycle Intersection ($\ge 3$):** In a $3$-connected graph, any two longest cycles
   intersect in at least $3$ vertices.
6. **Double Counting over $\mathrm{Aut}(G)$:**
   $3 n |\mathrm{Aut}(G)| \le n \sum_{\varphi \in \mathrm{Aut}(G)} |S \cap \varphi(S)| = k^2 |\mathrm{Aut}(G)|$,
   giving $k^2 \ge 3n$, hence $\sqrt{3n} \le k$.
-/

namespace OMA.LovaszBabai

open SimpleGraph LovaszConjecture

section Helpers

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Map a walk along a graph isomorphism. -/
def mapWalk (φ : G ≃g G) {u v : V} (p : G.Walk u v) : G.Walk (φ u) (φ v) :=
  p.map φ.toHom

lemma mapWalk_length (φ : G ≃g G) {u v : V} (p : G.Walk u v) :
    (mapWalk G φ p).length = p.length :=
  Walk.length_map _ _

lemma mapWalk_support (φ : G ≃g G) {u v : V} (p : G.Walk u v) :
    (mapWalk G φ p).support = p.support.map φ :=
  Walk.support_map _ _

lemma mapWalk_isCycle (φ : G ≃g G) {v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    (mapWalk G φ c).IsCycle :=
  hc.map φ.injective

/-- The vertex set of a walk as a Finset. -/
def walkVerts {u v : V} (p : G.Walk u v) : Finset V :=
  p.support.toFinset

lemma mem_walkVerts {u v w : V} {p : G.Walk u v} : w ∈ walkVerts G p ↔ w ∈ p.support :=
  List.mem_toFinset

lemma card_walkVerts_of_isCycle {v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    (walkVerts G c).card = c.length := by
  have htail_eq : c.support.toFinset = c.support.tail.toFinset := by
    ext x
    simp only [List.mem_toFinset]
    constructor
    · intro hx
      cases hs : c.support with
      | nil => simp [hs] at hx
      | cons a l =>
        rw [hs] at hx
        rcases List.mem_cons.mp hx with rfl | hl
        · have hstart : x = v := by
            have := c.cons_tail_support
            rw [hs] at this
            exact (List.cons.inj this).1.symm
          subst hstart
          have hcnt := hc.count_support
          rw [hs, List.count_cons_self] at hcnt
          have hpos : 0 < l.count x := by omega
          exact List.count_pos_iff.mp hpos
        · exact hl
    · intro hx
      exact List.mem_of_mem_tail hx
  rw [walkVerts, htail_eq, List.toFinset_card_of_nodup hc.support_nodup]
  have hlen := c.length_support
  cases hs : c.support with
  | nil => simp [hs] at hlen
  | cons a l =>
    rw [hs] at hlen
    simp at hlen ⊢
    omega

lemma cycle_length_le_card {v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    c.length ≤ Fintype.card V := by
  rw [← card_walkVerts_of_isCycle G hc]
  exact Finset.card_le_univ _

/-- In a vertex-transitive graph, all vertices have the same degree. -/
lemma degree_eq_of_isVertexTransitive (htrans : IsVertexTransitive G) (u v : V) :
    G.degree u = G.degree v := by
  obtain ⟨φ, rfl⟩ := htrans u v
  exact (φ.degree_eq u).symm

/-- A connected graph on n ≥ 3 vertices that is vertex-transitive has degree ≥ 2. -/
lemma two_le_degree_of_connected_trans (hconn : G.Connected) (htrans : IsVertexTransitive G)
    (hcard : 3 ≤ Fintype.card V) (v : V) : 2 ≤ G.degree v := by
  by_contra hlt
  push Not at hlt
  have hpos : 1 ≤ G.degree v := by
    have hne : ∃ w : V, w ≠ v := by
      by_contra hall; push Not at hall
      have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => (hall a).trans (hall b).symm
      omega
    obtain ⟨w, hw⟩ := hne
    obtain ⟨p⟩ := hconn v w
    cases p with
    | nil => exact absurd rfl hw
    | cons hadj _ =>
      exact Finset.card_pos.mpr ⟨_, (G.mem_neighborFinset _ _).mpr hadj⟩
  have hdeg1 : G.degree v = 1 := by omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hdeg1
  have huv : G.Adj v u := (G.mem_neighborFinset _ _).mp (hu ▸ Finset.mem_singleton_self u)
  have hdegu : G.degree u = 1 := by rw [degree_eq_of_isVertexTransitive G htrans u v, hdeg1]
  have hu_nbrs : G.neighborFinset u = {v} := by
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hdegu
    have hv_mem : v ∈ G.neighborFinset u := (G.mem_neighborFinset _ _).mpr huv.symm
    rw [hw, Finset.mem_singleton] at hv_mem
    rw [hw, hv_mem]
  -- Every vertex is in {v, u} by connectedness
  have hclosed_vu : ∀ a : V, (a = v ∨ a = u) → ∀ b : V, G.Adj a b → (b = v ∨ b = u) := by
    intro a ha b hab
    rcases ha with ha | ha
    · rw [ha] at hab
      right
      have hb : b ∈ G.neighborFinset v := (G.mem_neighborFinset _ _).mpr hab
      rw [hu, Finset.mem_singleton] at hb; exact hb
    · rw [ha] at hab
      left
      have hb : b ∈ G.neighborFinset u := (G.mem_neighborFinset _ _).mpr hab
      rw [hu_nbrs, Finset.mem_singleton] at hb; exact hb
  have hall : ∀ x : V, x = v ∨ x = u := by
    intro x
    obtain ⟨p⟩ := hconn v x
    have hstep : ∀ {a b : V} (q : G.Walk a b), (a = v ∨ a = u) → (b = v ∨ b = u) := by
      intro a b q
      induction q with
      | nil => exact id
      | cons hab _ ih => exact fun ha => ih (hclosed_vu _ ha _ hab)
    exact hstep p (Or.inl rfl)
  have hle2 : Fintype.card V ≤ 2 := by
    have hsub : (Finset.univ : Finset V) ⊆ {v, u} := fun x _ => by
      rcases hall x with rfl | rfl <;> simp
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  omega

/-- Every finite graph with minimum degree ≥ 2 contains a cycle. -/
lemma exists_cycle_of_two_le_degree [Nonempty V] (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
  classical
  -- Take a path of maximum length
  let S : Finset ℕ := (Finset.univ : Finset (Σ a b : V, {p : G.Walk a b // p.IsPath})).image (fun x => x.2.2.1.length)
  -- Instead, bound path length by Fintype.card V and use Finset.max' on reachable lengths
  let L : Finset ℕ := (Finset.range (Fintype.card V + 1)).filter
    (fun l => ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ p.length = l)
  have h0 : 0 ∈ L := by
    simp only [L, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Classical.arbitrary V, Classical.arbitrary V, Walk.nil, Walk.IsPath.nil, rfl⟩
  have hLne : L.Nonempty := ⟨0, h0⟩
  let m := L.max' hLne
  have hm_mem : m ∈ L := Finset.max'_mem L hLne
  obtain ⟨a, b, p, hp, hplen⟩ := (Finset.mem_filter.mp hm_mem).2
  -- Every neighbor of a must lie in p.support
  have hnbr_mem : ∀ w : V, G.Adj a w → w ∈ p.support := by
    intro w haw
    by_contra hnot
    let p' : G.Walk w b := Walk.cons haw.symm p
    have hp' : p'.IsPath := Walk.IsPath.cons hp hnot
    have hlen' : p'.length = m + 1 := by simp [p', hplen]
    have hle_card : p'.length < Fintype.card V + 1 := by
      have hnd : p'.support.Nodup := hp'.support_nodup
      have := List.toFinset_card_of_nodup hnd
      have hsub := Finset.card_le_univ p'.support.toFinset
      have hls := p'.length_support
      omega
    have hm1_mem : m + 1 ∈ L := by
      simp only [L, Finset.mem_filter, Finset.mem_range]
      exact ⟨hlen' ▸ hle_card, w, b, p', hp', hlen'⟩
    have := Finset.le_max' L (m + 1) hm1_mem
    omega
  -- p cannot be nil since deg a ≥ 2
  cases p with
  | nil =>
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < G.degree a by have := hdeg a; omega)
    have haw := (G.mem_neighborFinset _ _).mp hw
    have hmem := hnbr_mem w haw
    simp at hmem
    exact absurd hmem haw.ne'
  | @cons _ x _ hax q =>
    -- Since deg a ≥ 2, there is a neighbor w ≠ x of a
    have hex : ∃ w ∈ G.neighborFinset a, w ≠ x := by
      have h2 := hdeg a
      by_contra hall; push Not at hall
      have hsub : G.neighborFinset a ⊆ {x} := fun w hw => Finset.mem_singleton.mpr (hall w hw)
      have := (Finset.card_le_card hsub).trans (by simp : ({x} : Finset V).card ≤ 1)
      rw [← SimpleGraph.degree] at this
      omega
    obtain ⟨w, hw_mem, hwx⟩ := hex
    have haw : G.Adj a w := (G.mem_neighborFinset _ _).mp hw_mem
    have hw_sup : w ∈ (Walk.cons hax q).support := hnbr_mem w haw
    have hw_q : w ∈ q.support := by
      simp only [Walk.support_cons, List.mem_cons] at hw_sup
      exact hw_sup.resolve_left haw.ne'
    let r : G.Walk x w := q.takeUntil w hw_q
    have hr_path : r.IsPath := (hp.of_cons).takeUntil hw_q
    have ha_not_r : a ∉ r.support := fun h => by
      have ha_not_q : a ∉ q.support := (List.nodup_cons.mp hp.support_nodup).1
      exact ha_not_q (Walk.support_takeUntil_subset q hw_q h)
    let p1 : G.Walk a w := Walk.cons hax r
    have hp1 : p1.IsPath := Walk.IsPath.cons hr_path ha_not_r
    let c : G.Walk w w := Walk.cons haw.symm p1
    refine ⟨w, c, ?_⟩
    rw [Walk.cons_isCycle_iff]
    refine ⟨hp1, ?_⟩
    intro he
    -- s(w, a) ∈ p1.edges = s(a, x) :: r.edges
    simp only [p1, Walk.edges_cons, List.mem_cons] at he
    rcases he with heq | hr_e
    · rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact haw.ne' h1
      · exact hwx h1
    · exact ha_not_r (r.fst_mem_support_of_mem_edges (by simpa [Sym2.eq_swap] using hr_e))

/-- Case d = 2: a connected 2-regular finite graph on n ≥ 3 vertices has a Hamiltonian cycle of length n. -/
lemma case_deg_two (hconn : G.Connected) (hdeg2 : ∀ v : V, G.degree v = 2)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = Fintype.card V := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v, c, hc⟩ := exists_cycle_of_two_le_degree G (fun u => by rw [hdeg2 u])
  refine ⟨v, c, hc, ?_⟩
  rw [← card_walkVerts_of_isCycle G hc]
  -- Every vertex in walkVerts G c has 2 neighbors in walkVerts G c, so no edges leave walkVerts G c
  have hclosed : ∀ u ∈ walkVerts G c, ∀ w : V, G.Adj u w → w ∈ walkVerts G c := by
    intro u hu w huw
    have h2sub := hc.ncard_neighborSet_toSubgraph_eq_two (mem_walkVerts G |>.mp hu)
    -- All neighbors of u in c.toSubgraph are neighbors of u in G and lie in walkVerts G c
    have hsub : c.toSubgraph.neighborSet u ⊆ G.neighborSet u := fun z hz => c.toSubgraph.adj_sub hz
    have hfin : (G.neighborSet u).Finite := Set.toFinite _
    have hcard_G : (G.neighborSet u).ncard = 2 := by
      rw [Set.ncard_eq_toFinset_card _ hfin]
      convert hdeg2 u using 1
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset_def]
      congr 1; ext z; simp
    have heq : c.toSubgraph.neighborSet u = G.neighborSet u :=
      Set.eq_of_subset_of_ncard_le hsub (by omega) hfin
    have hw_sub : w ∈ c.toSubgraph.neighborSet u := heq ▸ huw
    have hw_verts : w ∈ c.toSubgraph.verts := c.toSubgraph.edge_vert hw_sub.symm
    exact (mem_walkVerts G).mpr (by simpa [Walk.verts_toSubgraph] using hw_verts)
  -- By connectedness, every vertex is in walkVerts G c
  have hall : walkVerts G c = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro x
    obtain ⟨p⟩ := hconn v x
    have hv : v ∈ walkVerts G c := (mem_walkVerts G).mpr (Walk.start_mem_support c)
    -- Walk induction from v to x
    have hstep : ∀ {a b : V} (q : G.Walk a b), a ∈ walkVerts G c → b ∈ walkVerts G c := by
      intro a b q
      induction q with
      | nil => exact id
      | cons hadj _ ih => exact fun ha => ih (hclosed _ ha _ hadj)
    exact hstep p hv
  rw [hall, Finset.card_univ]

end Helpers

section Connectivity

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Two vertices are connected in G - S. -/
def ReachAvoiding (S : Finset V) (u v : V) : Prop :=
  ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∉ S

lemma reachAvoiding_refl {S : Finset V} {u : V} (hu : u ∉ S) : ReachAvoiding G S u u :=
  ⟨Walk.nil, fun w hw => by simp only [Walk.support_nil, List.mem_singleton] at hw; subst hw; exact hu⟩

lemma reachAvoiding_symm {S : Finset V} {u v : V} (h : ReachAvoiding G S u v) :
    ReachAvoiding G S v u := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, fun w hw => hp w (by simpa using hw)⟩

lemma reachAvoiding_trans {S : Finset V} {u v w : V}
    (h1 : ReachAvoiding G S u v) (h2 : ReachAvoiding G S v w) :
    ReachAvoiding G S u w := by
  obtain ⟨p1, hp1⟩ := h1
  obtain ⟨p2, hp2⟩ := h2
  refine ⟨p1.append p2, fun x hx => ?_⟩
  rcases (Walk.mem_support_append_iff p1 p2).mp hx with h | h
  · exact hp1 x h
  · exact hp2 x h

/-- The connected component of u in G - S as a Finset. -/
noncomputable def compAvoiding (S : Finset V) (u : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ReachAvoiding G S u v)

lemma mem_compAvoiding {S : Finset V} {u v : V} :
    v ∈ compAvoiding G S u ↔ ReachAvoiding G S u v := by
  classical simp [compAvoiding]

lemma self_mem_compAvoiding {S : Finset V} {u : V} (hu : u ∉ S) :
    u ∈ compAvoiding G S u :=
  (mem_compAvoiding G).mpr (reachAvoiding_refl G hu)

lemma compAvoiding_disjoint_S {S : Finset V} {u : V} :
    Disjoint (compAvoiding G S u) S := by
  rw [Finset.disjoint_left]
  intro x hx hxS
  obtain ⟨p, hp⟩ := (mem_compAvoiding G).mp hx
  exact hp x (Walk.end_mem_support p) hxS

lemma compAvoiding_closed {S : Finset V} {u a b : V}
    (ha : a ∈ compAvoiding G S u) (hab : G.Adj a b) (hbS : b ∉ S) :
    b ∈ compAvoiding G S u := by
  rw [mem_compAvoiding] at ha ⊢
  exact reachAvoiding_trans G ha ⟨Walk.cons hab Walk.nil, fun w hw => by
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · rw [h]; obtain ⟨p, hp⟩ := ha; exact hp a (Walk.end_mem_support p)
    · rw [h]; exact hbS⟩

/-- S is a separating set if G - S has at least two vertices not connected avoiding S. -/
def IsSeparating (S : Finset V) : Prop :=
  ∃ u v : V, u ∉ S ∧ v ∉ S ∧ ¬ ReachAvoiding G S u v

/-- A separating set S separates a nonempty subset X ⊆ V \ S from V \ (X ∪ S). -/
lemma isSeparating_of_closed_subset {S X : Finset V}
    (hXne : X.Nonempty) (hXdisj : Disjoint X S)
    (hYne : (Finset.univ \ (X ∪ S)).Nonempty)
    (hclosed : ∀ a ∈ X, ∀ b : V, G.Adj a b → b ∈ X ∪ S) :
    IsSeparating G S := by
  obtain ⟨u, huX⟩ := hXne
  obtain ⟨v, hvY⟩ := hYne
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or] at hvY
  refine ⟨u, v, Finset.disjoint_left.mp hXdisj huX, hvY.2, fun ⟨p, hp⟩ => ?_⟩
  have hstay : ∀ {a b : V} (q : G.Walk a b), a ∈ X → (∀ w ∈ q.support, w ∉ S) → b ∈ X := by
    intro a b q
    induction q with
    | nil => intro ha _; exact ha
    | @cons a c b hac r ih =>
      intro ha hq
      have hcS : c ∉ S := hq c (by simp)
      have hcXS := hclosed a ha c hac
      have hcX : c ∈ X := (Finset.mem_union.mp hcXS).resolve_right hcS
      exact ih hcX (fun w hw => hq w (by simp [hw]))
  exact hvY.1 (hstay p huX hp)

/-- Every component of G - S inside a closed subset X has size ≤ |X|. -/
lemma card_compAvoiding_le_of_closed {S X : Finset V} {u : V}
    (huX : u ∈ X) (hXdisj : Disjoint X S)
    (hclosed : ∀ a ∈ X, ∀ b : V, G.Adj a b → b ∈ X ∪ S) :
    (compAvoiding G S u).card ≤ X.card := by
  apply Finset.card_le_card
  intro v hv
  obtain ⟨p, hp⟩ := (mem_compAvoiding G).mp hv
  have hstay : ∀ {a b : V} (q : G.Walk a b), a ∈ X → (∀ w ∈ q.support, w ∉ S) → b ∈ X := by
    intro a b q
    induction q with
    | nil => intro ha _; exact ha
    | @cons a c b hac r ih =>
      intro ha hq
      have hcS : c ∉ S := hq c (by simp)
      have hcX : c ∈ X := (Finset.mem_union.mp (hclosed a ha c hac)).resolve_right hcS
      exact ih hcX (fun w hw => hq w (by simp [hw]))
  exact hstay p huX hp

/-- Map a separating set and component under a graph isomorphism. -/
lemma isSeparating_image (φ : G ≃g G) {S : Finset V} (hS : IsSeparating G S) :
    IsSeparating G (S.image φ) := by
  obtain ⟨u, v, hu, hv, hnr⟩ := hS
  refine ⟨φ u, φ v, ?_, ?_, ?_⟩
  · intro h; obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h; exact hu (φ.injective hxe ▸ hx)
  · intro h; obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h; exact hv (φ.injective hxe ▸ hx)
  · rintro ⟨p, hp⟩
    apply hnr
    refine ⟨(p.map φ.symm.toHom).copy (φ.symm_apply_apply u) (φ.symm_apply_apply v), fun w hw => ?_⟩
    rw [Walk.support_copy, Walk.support_map, List.mem_map] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    intro hmem
    exact hp z hz (Finset.mem_image.mpr ⟨φ.symm z, hmem, φ.apply_symm_apply z⟩)

lemma compAvoiding_image (φ : G ≃g G) (S : Finset V) (u : V) :
    compAvoiding G (S.image φ) (φ u) = (compAvoiding G S u).image φ := by
  ext y
  simp only [mem_compAvoiding, Finset.mem_image]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨φ.symm y, ⟨(p.map φ.symm.toHom).copy (φ.symm_apply_apply u) rfl, fun w hw => ?_⟩, φ.apply_symm_apply y⟩
    rw [Walk.support_copy, Walk.support_map, List.mem_map] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    intro hmem
    exact hp z hz (Finset.mem_image.mpr ⟨φ.symm z, hmem, φ.apply_symm_apply z⟩)
  · rintro ⟨x, ⟨p, hp⟩, rfl⟩
    refine ⟨p.map φ.toHom, fun w hw => ?_⟩
    rw [Walk.support_map, List.mem_map] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    intro hmem
    obtain ⟨t, ht, hte⟩ := Finset.mem_image.mp hmem
    exact hp z hz (φ.injective hte ▸ ht)

set_option maxHeartbeats 800000 in
/-- Watkins' 3-connectivity theorem: every connected vertex-transitive graph of degree d ≥ 3
has no separating set of size ≤ 2. -/
lemma no_separating_le_two (hconn : G.Connected) (htrans : IsVertexTransitive G)
    (hdeg3 : ∀ v : V, 3 ≤ G.degree v) (S0 : Finset V) (hS0 : S0.card ≤ 2) :
    ¬ IsSeparating G S0 := by
  classical
  intro hsep0
  -- Let κ be the minimum cardinality of a separating set (κ ∈ {1, 2})
  have hex_κ : ∃ k : ℕ, ∃ S : Finset V, S.card = k ∧ IsSeparating G S := ⟨S0.card, S0, rfl, hsep0⟩
  let κ := Nat.find hex_κ
  have hκ_spec : ∃ S : Finset V, S.card = κ ∧ IsSeparating G S := Nat.find_spec hex_κ
  have hκ_min : ∀ S : Finset V, IsSeparating G S → κ ≤ S.card := fun S hS =>
    Nat.find_min' hex_κ ⟨S, rfl, hS⟩
  have hκ_le2 : κ ≤ 2 := (hκ_min S0 hsep0).trans hS0
  have hκ_pos : 1 ≤ κ := by
    obtain ⟨S, hSc, u, v, _, _, hnr⟩ := hκ_spec
    by_contra h0
    have hSe : S = ∅ := Finset.card_eq_zero.mp (by omega)
    obtain ⟨p⟩ := hconn u v
    exact hnr ⟨p, fun w _ => by simp [hSe]⟩
  -- Let a be the minimum cardinality of a component of G - S over all minimum separating sets S
  have hex_a : ∃ m : ℕ, ∃ (S : Finset V) (u : V),
      S.card = κ ∧ IsSeparating G S ∧ u ∉ S ∧ (compAvoiding G S u).card = m := by
    obtain ⟨S, hSc, u, _, hu, _, _⟩ := hκ_spec
    exact ⟨(compAvoiding G S u).card, S, u, hSc, ⟨u, _, hu, by assumption, by assumption⟩, hu, rfl⟩
  let a := Nat.find hex_a
  obtain ⟨S, u0, hScard, hSsep, hu0S, hAcard⟩ := Nat.find_spec hex_a
  have ha_min : ∀ (T : Finset V) (w : V), T.card = κ → IsSeparating G T → w ∉ T →
      a ≤ (compAvoiding G T w).card := fun T w hTc hTs hw =>
    Nat.find_min' hex_a ⟨T, w, hTc, hTs, hw, rfl⟩
  set A := compAvoiding G S u0
  set A' := Finset.univ \ (A ∪ S)
  have hA_disj_S : Disjoint A S := compAvoiding_disjoint_S G
  have hA_closed : ∀ x ∈ A, ∀ y : V, G.Adj x y → y ∈ A ∪ S := fun x hx y hxy => by
    by_cases hyS : y ∈ S
    · exact Finset.mem_union_right _ hyS
    · exact Finset.mem_union_left _ (compAvoiding_closed G hx hxy hyS)
  have hA'_ne : A'.Nonempty := by
    obtain ⟨x, y, hxS, hyS, hnr⟩ := hSsep
    by_cases hxA : x ∈ A
    · refine ⟨y, ?_⟩
      simp only [A', Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
      exact ⟨fun hyA => hnr (reachAvoiding_trans G (reachAvoiding_symm G ((mem_compAvoiding G).mp hxA)) ((mem_compAvoiding G).mp hyA)), hyS⟩
    · refine ⟨x, ?_⟩
      simp only [A', Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
      exact ⟨hxA, hxS⟩
  have hA'_card : a ≤ A'.card := by
    obtain ⟨w, hw⟩ := hA'_ne
    simp only [A', Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or] at hw
    have hcomp_sub : compAvoiding G S w ⊆ A' := by
      intro z hz
      simp only [A', Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
      refine ⟨fun hzA => hw.1 ((mem_compAvoiding G).mpr (reachAvoiding_trans G ((mem_compAvoiding G).mp hzA) (reachAvoiding_symm G ((mem_compAvoiding G).mp hz)))),
        Finset.disjoint_left.mp (compAvoiding_disjoint_S G) hz⟩
    exact (ha_min S w hScard hSsep hw.2).trans (Finset.card_le_card hcomp_sub)
  -- Lower bound: a + κ ≥ d + 1 ≥ 4
  have ha_ge : 4 ≤ a + κ := by
    have hu0A : u0 ∈ A := self_mem_compAvoiding G hu0S
    have hnbr_sub : G.neighborFinset u0 ⊆ (A.erase u0) ∪ S := by
      intro w hw
      have hadj := (G.mem_neighborFinset _ _).mp hw
      rcases Finset.mem_union.mp (hA_closed u0 hu0A w hadj) with hwA | hwS
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hadj.ne', hwA⟩)
      · exact Finset.mem_union_right _ hwS
    have hcard_le := (Finset.card_le_card hnbr_sub).trans (Finset.card_union_le _ _)
    have hAcard' : A.card = a := hAcard
    rw [Finset.card_erase_of_mem hu0A, hAcard', hScard] at hcard_le
    have hd3 := hdeg3 u0
    rw [SimpleGraph.degree] at hd3
    have ha_pos : 1 ≤ a := by rw [← hAcard']; exact Finset.card_pos.mpr ⟨u0, hu0A⟩
    omega
  -- Key step: prove κ < a! (Rules out κ = 2, a = 2, d = 3 via triangle count)
  have hκ_lt_a : κ < a := by
    by_contra hle
    push Not at hle
    have hκ2 : κ = 2 := by omega
    have ha2 : a = 2 := by omega
    have hu0A : u0 ∈ A := self_mem_compAvoiding G hu0S
    have hAcard' : A.card = a := hAcard
    obtain ⟨v0, hv0A, hv0ne⟩ : ∃ v0 ∈ A, v0 ≠ u0 :=
      Finset.exists_mem_ne (by omega) u0
    have hA_eq : A = {u0, v0} := by
      apply (Finset.eq_of_subset_of_card_le _ _).symm
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      · rw [Finset.card_pair hv0ne.symm, hAcard', ha2]
    obtain ⟨s1, s2, hs12, hS_eq⟩ : ∃ s1 s2 : V, s1 ≠ s2 ∧ S = {s1, s2} :=
      Finset.card_eq_two.mp (hScard.trans hκ2)
    have hu0_nbrs : G.neighborFinset u0 = {v0, s1, s2} := by
      have hsub : G.neighborFinset u0 ⊆ {v0, s1, s2} := by
        intro w hw
        have hadj := (G.mem_neighborFinset _ _).mp hw
        rcases Finset.mem_union.mp (hA_closed u0 hu0A w hadj) with hwA | hwS
        · rw [hA_eq, Finset.mem_insert, Finset.mem_singleton] at hwA
          rcases hwA with rfl | rfl
          · exact absurd rfl hadj.ne
          · simp
        · rw [hS_eq, Finset.mem_insert, Finset.mem_singleton] at hwS
          rcases hwS with rfl | rfl <;> simp
      have hcard3 : ({v0, s1, s2} : Finset V).card ≤ 3 :=
        (Finset.card_insert_le _ _).trans (by have := Finset.card_le_two (a := s1) (b := s2); omega)
      have hd3 := hdeg3 u0
      rw [SimpleGraph.degree] at hd3
      exact Finset.eq_of_subset_of_card_le hsub (by omega)
    have hv0_nbrs : G.neighborFinset v0 = {u0, s1, s2} := by
      have hsub : G.neighborFinset v0 ⊆ {u0, s1, s2} := by
        intro w hw
        have hadj := (G.mem_neighborFinset _ _).mp hw
        rcases Finset.mem_union.mp (hA_closed v0 hv0A w hadj) with hwA | hwS
        · rw [hA_eq, Finset.mem_insert, Finset.mem_singleton] at hwA
          rcases hwA with rfl | rfl
          · simp
          · exact absurd rfl hadj.ne
        · rw [hS_eq, Finset.mem_insert, Finset.mem_singleton] at hwS
          rcases hwS with rfl | rfl <;> simp
      have hcard3 : ({u0, s1, s2} : Finset V).card ≤ 3 :=
        (Finset.card_insert_le _ _).trans (by have := Finset.card_le_two (a := s1) (b := s2); omega)
      have hd3 := hdeg3 v0
      rw [SimpleGraph.degree] at hd3
      exact Finset.eq_of_subset_of_card_le hsub (by omega)
    have hd_all3 : ∀ w : V, G.degree w = 3 := by
      intro w
      rw [degree_eq_of_isVertexTransitive G htrans w u0]
      have hd3 := hdeg3 u0
      have hle3 : G.degree u0 ≤ 3 := by
        rw [SimpleGraph.degree, hu0_nbrs]
        exact (Finset.card_insert_le _ _).trans (by have := Finset.card_le_two (a := s1) (b := s2); omega)
      omega
    -- s1 is adjacent to u0, v0, and at least one vertex z ∈ A' (else {s2} would be a 1-cut!)
    have hs1_u0 : G.Adj s1 u0 := ((G.mem_neighborFinset _ _).mp (hu0_nbrs ▸ by simp)).symm
    have hs1_v0 : G.Adj s1 v0 := ((G.mem_neighborFinset _ _).mp (hv0_nbrs ▸ by simp)).symm
    have hv0_s2 : G.Adj v0 s2 := (G.mem_neighborFinset _ _).mp (hv0_nbrs ▸ by simp)
    have hex_z : ∃ z ∈ A', G.Adj s1 z := by
      by_contra hno; push Not at hno
      -- Then {s2} separates A ∪ {s1} from A', contradicting κ = 2!
      have h1sep : IsSeparating G {s2} := by
        refine isSeparating_of_closed_subset G (X := A ∪ {s1}) ⟨u0, Finset.mem_union_left {s1} hu0A⟩ ?_ ?_ ?_
        · rw [Finset.disjoint_singleton_right, Finset.mem_union, not_or]
          exact ⟨fun h => Finset.disjoint_left.mp hA_disj_S h (hS_eq ▸ by simp), by simp [hs12.symm]⟩
        · obtain ⟨w, hw⟩ := hA'_ne
          refine ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          simp only [A', Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or] at hw ⊢
          refine ⟨⟨hw.1, ?_⟩, ?_⟩
          · intro heq; rw [Finset.mem_singleton] at heq; subst heq; exact hw.2 (hS_eq ▸ by simp)
          · intro heq; rw [Finset.mem_singleton] at heq; subst heq; exact hw.2 (hS_eq ▸ by simp)
        · intro x hx y hxy
          rcases Finset.mem_union.mp hx with hxA | hx1
          · rcases Finset.mem_union.mp (hA_closed x hxA y hxy) with hyA | hyS
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ hyA)
            · rw [hS_eq, Finset.mem_insert, Finset.mem_singleton] at hyS
              rcases hyS with rfl | rfl
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
              · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
          · rw [Finset.mem_singleton] at hx1; subst hx1
            by_cases hyA : y ∈ A
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ hyA)
            · by_cases hyS : y ∈ S
              · rw [hS_eq, Finset.mem_insert, Finset.mem_singleton] at hyS
                rcases hyS with rfl | rfl
                · exact absurd rfl hxy.ne
                · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
              · exfalso
                exact hno y (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hyA, hyS]⟩) hxy
      have := hκ_min {s2} h1sep; simp at this; omega
    obtain ⟨z, hzA', hs1z⟩ := hex_z
    have hz_ne_u0 : z ≠ u0 := by intro h; subst h; simp [A', hu0A] at hzA'
    have hz_ne_v0 : z ≠ v0 := by intro h; subst h; simp [A', hv0A] at hzA'
    have hs1_nbrs : G.neighborFinset s1 = {u0, v0, z} := by
      have hsub : {u0, v0, z} ⊆ G.neighborFinset s1 := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> exact (G.mem_neighborFinset _ _).mpr (by assumption)
      have h3 : ({u0, v0, z} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair hz_ne_v0.symm]
        simp [hv0ne.symm, hz_ne_u0.symm]
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [h3, ← SimpleGraph.degree, hd_all3 s1])).symm
    -- Count ordered adjacent pairs in N(v): invariant under Aut(G)!
    let triCount (w : V) : ℕ :=
      ((G.neighborFinset w ×ˢ G.neighborFinset w).filter (fun p => G.Adj p.1 p.2)).card
    -- triCount u0 ≥ 4: (v0, s1), (s1, v0), (v0, s2), (s2, v0)
    have htri_u0 : 4 ≤ triCount u0 := by
      let pairs : Finset (V × V) := {(v0, s1), (s1, v0), (v0, s2), (s2, v0)}
      have hsub : pairs ⊆ (G.neighborFinset u0 ×ˢ G.neighborFinset u0).filter (fun p => G.Adj p.1 p.2) := by
        intro p hp
        simp only [pairs, Finset.mem_insert, Finset.mem_singleton] at hp
        rw [Finset.mem_filter, Finset.mem_product, hu0_nbrs]
        rcases hp with rfl | rfl | rfl | rfl
        · exact ⟨⟨by simp, by simp⟩, hs1_v0.symm⟩
        · exact ⟨⟨by simp, by simp⟩, hs1_v0⟩
        · exact ⟨⟨by simp, by simp⟩, hv0_s2⟩
        · exact ⟨⟨by simp, by simp⟩, hv0_s2.symm⟩
      have hcard4 : pairs.card = 4 := by
        have hv0_ne_s1 : v0 ≠ s1 := hs1_v0.ne'
        have hv0_ne_s2 : v0 ≠ s2 := hv0_s2.ne
        simp only [pairs]
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [hv0_ne_s2]
        · simp [hs12, hv0_ne_s1.symm]
        · simp [hv0_ne_s1, hv0_ne_s2, hs12, hv0_ne_s1.symm]
      exact hcard4 ▸ Finset.card_le_card hsub
    -- triCount s1 ≤ 2: z ∈ A' is not adjacent to u0 or v0 ∈ A!
    have htri_s1 : triCount s1 ≤ 2 := by
      have hsub : (G.neighborFinset s1 ×ˢ G.neighborFinset s1).filter (fun p => G.Adj p.1 p.2) ⊆
          {(u0, v0), (v0, u0)} := by
        intro ⟨p1, p2⟩ hp
        rw [Finset.mem_filter, Finset.mem_product, hs1_nbrs] at hp
        rcases hp with ⟨⟨hp1, hp2⟩, hadj⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp1 hp2 ⊢
        have hnot_u0z : ¬ G.Adj u0 z := fun h => by
          have hzAS := hA_closed u0 hu0A z h
          simp only [A', Finset.mem_sdiff] at hzA'; exact hzA'.2 hzAS
        have hnot_v0z : ¬ G.Adj v0 z := fun h => by
          have hzAS := hA_closed v0 hv0A z h
          simp only [A', Finset.mem_sdiff] at hzA'; exact hzA'.2 hzAS
        rcases hp1 with rfl | rfl | rfl <;> rcases hp2 with rfl | rfl | rfl
        · exact absurd rfl hadj.ne
        · left; rfl
        · exact absurd hadj hnot_u0z
        · right; rfl
        · exact absurd rfl hadj.ne
        · exact absurd hadj hnot_v0z
        · exact absurd hadj.symm hnot_u0z
        · exact absurd hadj.symm hnot_v0z
        · exact absurd rfl hadj.ne
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    -- Vertex-transitivity forces triCount u0 = triCount s1!
    obtain ⟨ψ, hψ⟩ := htrans u0 s1
    have htri_eq : triCount u0 = triCount s1 := by
      apply Finset.card_bij (fun p _ => (ψ p.1, ψ p.2))
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, SimpleGraph.mem_neighborFinset] at hp ⊢
        rw [← hψ]
        exact ⟨⟨ψ.map_rel_iff.mpr hp.1.1, ψ.map_rel_iff.mpr hp.1.2⟩, ψ.map_rel_iff.mpr hp.2⟩
      · intro a _ b _ hab
        exact Prod.ext (ψ.injective (congrArg Prod.fst hab)) (ψ.injective (congrArg Prod.snd hab))
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_product, SimpleGraph.mem_neighborFinset] at hq
        refine ⟨(ψ.symm q.1, ψ.symm q.2), ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_product, SimpleGraph.mem_neighborFinset]
        have h1 : G.Adj (ψ.symm s1) (ψ.symm q.1) := ψ.symm.map_rel_iff.mpr hq.1.1
        have h2 : G.Adj (ψ.symm s1) (ψ.symm q.2) := ψ.symm.map_rel_iff.mpr hq.1.2
        rw [← hψ, ψ.symm_apply_apply] at h1 h2
        exact ⟨⟨h1, h2⟩, ψ.symm.map_rel_iff.mpr hq.2⟩
    omega
  -- Now κ < a! Pick x ∈ S and an automorphism φ sending u0 to x.
  obtain ⟨x, hxS⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨φ, hφ⟩ := htrans u0 x
  set T := S.image φ
  set B := compAvoiding G T x
  set B' := Finset.univ \ (B ∪ T)
  have hTcard : T.card = κ := by rw [Finset.card_image_of_injective _ φ.injective, hScard]
  have hTsep : IsSeparating G T := isSeparating_image G φ hSsep
  have hB_eq : B = A.image φ := by simp only [B, A, T]; rw [← hφ]; exact compAvoiding_image G φ S u0
  have hBcard : B.card = a := by rw [hB_eq, Finset.card_image_of_injective _ φ.injective, hAcard]
  have hB_disj_T : Disjoint B T := compAvoiding_disjoint_S G
  have hB_closed : ∀ y ∈ B, ∀ z : V, G.Adj y z → z ∈ B ∪ T := fun y hy z hyz => by
    by_cases hzT : z ∈ T
    · exact Finset.mem_union_right _ hzT
    · exact Finset.mem_union_left _ (compAvoiding_closed G hy hyz hzT)
  have hxB : x ∈ B := by rw [hB_eq]; exact Finset.mem_image.mpr ⟨u0, self_mem_compAvoiding G hu0S, hφ⟩
  have hB'_card : a ≤ B'.card := by
    have hB'_eq : B' = A'.image φ := by
      ext y
      simp only [B', A', Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, Finset.mem_image, hB_eq, T, not_or]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨φ.symm y, ⟨fun hA => h1 ⟨φ.symm y, hA, φ.apply_symm_apply y⟩,
          fun hS => h2 ⟨φ.symm y, hS, φ.apply_symm_apply y⟩⟩, φ.apply_symm_apply y⟩
      · rintro ⟨z, ⟨hzA, hzS⟩, rfl⟩
        exact ⟨fun ⟨w, hwA, hwe⟩ => hzA (φ.injective hwe ▸ hwA), fun ⟨w, hwS, hwe⟩ => hzS (φ.injective hwe ▸ hwS)⟩
    rw [hB'_eq, Finset.card_image_of_injective _ φ.injective]; exact hA'_card
  -- Helper: given closed X1 (boundary U1) and closed X2 (boundary U2) disjoint from each other
  -- with U1.card + U2.card ≤ 2 * κ and X1.Nonempty, X2.Nonempty, X1.card < a: contradiction!
  have hsplit_contra : ∀ (X1 X2 U1 U2 : Finset V),
      X1.Nonempty → X2.Nonempty →
      Disjoint X1 U1 → Disjoint X2 U1 → Disjoint X1 X2 →
      Disjoint X2 U2 → Disjoint X1 U2 →
      (∀ y ∈ X1, ∀ z : V, G.Adj y z → z ∈ X1 ∪ U1) →
      (∀ y ∈ X2, ∀ z : V, G.Adj y z → z ∈ X2 ∪ U2) →
      U1.card + U2.card ≤ 2 * κ → X1.card < a → False := by
    intro X1 X2 U1 U2 hX1ne hX2ne hX1U1 hX2U1 hX12 hX2U2 hX1U2 hcl1 hcl2 hsum hlt
    have hU1_sep : IsSeparating G U1 := by
      refine isSeparating_of_closed_subset G hX1ne hX1U1 ?_ hcl1
      obtain ⟨y, hy⟩ := hX2ne
      exact ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
        rw [Finset.mem_union, not_or]
        exact ⟨Finset.disjoint_right.mp hX12 hy, Finset.disjoint_left.mp hX2U1 hy⟩⟩⟩
    have hU2_sep : IsSeparating G U2 := by
      refine isSeparating_of_closed_subset G hX2ne hX2U2 ?_ hcl2
      obtain ⟨y, hy⟩ := hX1ne
      exact ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
        rw [Finset.mem_union, not_or]
        exact ⟨Finset.disjoint_left.mp hX12 hy, Finset.disjoint_left.mp hX1U2 hy⟩⟩⟩
    have h1 := hκ_min U1 hU1_sep
    have h2 := hκ_min U2 hU2_sep
    have hU1eq : U1.card = κ := by omega
    obtain ⟨w, hw⟩ := hX1ne
    have hcomp_le := card_compAvoiding_le_of_closed G hw hX1U1 hcl1
    have hge := ha_min U1 w hU1eq hU1_sep (Finset.disjoint_left.mp hX1U1 hw)
    omega
  -- Helper: A' is closed with boundary S, B' is closed with boundary T
  have hA'_closed : ∀ y ∈ A', ∀ z : V, G.Adj y z → z ∈ A' ∪ S := by
    intro y hy z hyz
    simp only [A', Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or] at hy ⊢
    by_cases hzS : z ∈ S
    · exact Or.inr hzS
    · left
      refine ⟨fun hzA => ?_, hzS⟩
      rcases Finset.mem_union.mp (hA_closed z hzA y hyz.symm) with hyA | hyS
      · exact hy.1 hyA
      · exact hy.2 hyS
  have hB'_closed : ∀ y ∈ B', ∀ z : V, G.Adj y z → z ∈ B' ∪ T := by
    intro y hy z hyz
    simp only [B', Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or] at hy ⊢
    by_cases hzT : z ∈ T
    · exact Or.inr hzT
    · left
      refine ⟨fun hzB => ?_, hzT⟩
      rcases Finset.mem_union.mp (hB_closed z hzB y hyz.symm) with hyB | hyT
      · exact hy.1 hyB
      · exact hy.2 hyT
  -- Step 1: Prove A ∩ B = ∅
  have hAB_empty : Disjoint A B := by
    by_contra hnot
    rw [Finset.not_disjoint_iff] at hnot
    obtain ⟨w, hwA, hwB⟩ := hnot
    have hAB_lt : (A ∩ B).card < a := by
      rw [← hBcard]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.inter_subset_right, fun heq => ?_⟩
      have hxA : x ∈ A := (Finset.mem_inter.mp (heq ▸ hxB)).1
      exact Finset.disjoint_left.mp hA_disj_S hxA hxS
    by_cases hA'B' : (A' ∩ B').Nonempty
    · -- Use U1 = (S ∩ B) ∪ (S ∩ T) ∪ (T ∩ A) and U2 = (S ∩ B') ∪ (S ∩ T) ∪ (T ∩ A')
      let U1 := (S ∩ (B ∪ T)) ∪ (T ∩ A)
      let U2 := (S ∩ (B' ∪ T)) ∪ (T ∩ A')
      have hsum : U1.card + U2.card ≤ 2 * κ := by
        -- Every element of S ∩ T is in both, every other element of S ∪ T is in at most one
        have hU1_sub : U1 ⊆ (S ∩ B) ∪ (S ∩ T) ∪ (T ∩ A) := by
          intro z hz; simp only [U1, Finset.mem_union, Finset.mem_inter] at hz ⊢; tauto
        have hU2_sub : U2 ⊆ (S ∩ B') ∪ (S ∩ T) ∪ (T ∩ A') := by
          intro z hz; simp only [U2, Finset.mem_union, Finset.mem_inter] at hz ⊢; tauto
        have h1 : U1.card ≤ (S ∩ B).card + (S ∩ T).card + (T ∩ A).card :=
          (Finset.card_le_card hU1_sub).trans ((Finset.card_union_le _ _).trans (by gcongr; exact Finset.card_union_le _ _))
        have h2 : U2.card ≤ (S ∩ B').card + (S ∩ T).card + (T ∩ A').card :=
          (Finset.card_le_card hU2_sub).trans ((Finset.card_union_le _ _).trans (by gcongr; exact Finset.card_union_le _ _))
        have hS_part : (S ∩ B).card + (S ∩ T).card + (S ∩ B').card ≤ S.card := by
          have hd1 : Disjoint (S ∩ B) (S ∩ T) := Finset.disjoint_left.mpr fun z h1 h2 =>
            Finset.disjoint_left.mp hB_disj_T (Finset.mem_inter.mp h1).2 (Finset.mem_inter.mp h2).2
          have hd2 : Disjoint ((S ∩ B) ∪ (S ∩ T)) (S ∩ B') := Finset.disjoint_left.mpr fun z h1 h2 => by
            have hzB' := (Finset.mem_inter.mp h2).2
            simp only [B', Finset.mem_sdiff, Finset.mem_union, not_or] at hzB'
            rcases Finset.mem_union.mp h1 with h | h
            · exact hzB'.2.1 (Finset.mem_inter.mp h).2
            · exact hzB'.2.2 (Finset.mem_inter.mp h).2
          rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2]
          apply Finset.card_le_card
          intro z hz; simp only [Finset.mem_union, Finset.mem_inter] at hz; tauto
        have hT_part : (T ∩ A).card + (S ∩ T).card + (T ∩ A').card ≤ T.card := by
          have hST : S ∩ T = T ∩ S := Finset.inter_comm S T
          rw [hST]
          have hd1 : Disjoint (T ∩ A) (T ∩ S) := Finset.disjoint_left.mpr fun z h1 h2 =>
            Finset.disjoint_left.mp hA_disj_S (Finset.mem_inter.mp h1).2 (Finset.mem_inter.mp h2).2
          have hd2 : Disjoint ((T ∩ A) ∪ (T ∩ S)) (T ∩ A') := Finset.disjoint_left.mpr fun z h1 h2 => by
            have hzA' := (Finset.mem_inter.mp h2).2
            simp only [A', Finset.mem_sdiff, Finset.mem_union, not_or] at hzA'
            rcases Finset.mem_union.mp h1 with h | h
            · exact hzA'.2.1 (Finset.mem_inter.mp h).2
            · exact hzA'.2.2 (Finset.mem_inter.mp h).2
          rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2]
          apply Finset.card_le_card
          intro z hz; simp only [Finset.mem_union, Finset.mem_inter] at hz; tauto
        omega
      exact hsplit_contra (A ∩ B) (A' ∩ B') U1 U2 ⟨w, Finset.mem_inter.mpr ⟨hwA, hwB⟩⟩ hA'B'
        (Finset.disjoint_left.mpr fun z h1 h2 => by
          simp only [U1, Finset.mem_inter, Finset.mem_union] at h1 h2
          rcases h2 with ⟨hzS, _⟩ | ⟨hzT, _⟩
          · exact Finset.disjoint_left.mp hA_disj_S h1.1 hzS
          · exact Finset.disjoint_left.mp hB_disj_T h1.2 hzT)
        (Finset.disjoint_left.mpr fun z h1 h2 => by
          simp only [U1, A', B', Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, not_or] at h1 h2
          tauto)
        (Finset.disjoint_left.mpr fun z h1 h2 => by
          simp only [A', Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union, not_or] at h1 h2
          exact h2.1.2.1 h1.1)
        (Finset.disjoint_left.mpr fun z h1 h2 => by
          simp only [U2, A', B', Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, not_or] at h1 h2
          tauto)
        (Finset.disjoint_left.mpr fun z h1 h2 => by
          simp only [U2, Finset.mem_inter, Finset.mem_union] at h1 h2
          rcases h2 with ⟨hzS, _⟩ | ⟨hzT, _⟩
          · exact Finset.disjoint_left.mp hA_disj_S h1.1 hzS
          · exact Finset.disjoint_left.mp hB_disj_T h1.2 hzT)
        (fun y hy z hyz => by
          obtain ⟨hyA, hyB⟩ := Finset.mem_inter.mp hy
          have h1 := hA_closed y hyA z hyz
          have h2 := hB_closed y hyB z hyz
          simp only [U1, Finset.mem_union, Finset.mem_inter] at h1 h2 ⊢; tauto)
        (fun y hy z hyz => by
          obtain ⟨hyA', hyB'⟩ := Finset.mem_inter.mp hy
          have h1 := hA'_closed y hyA' z hyz
          have h2 := hB'_closed y hyB' z hyz
          simp only [U2, Finset.mem_union, Finset.mem_inter] at h1 h2 ⊢; tauto)
        hsum hAB_lt
    · -- A' ∩ B' = ∅: then A' ⊆ B ∪ T and B' ⊆ A ∪ S; since a > κ, A' ∩ B ≠ ∅ and A ∩ B' ≠ ∅
      rw [Finset.not_nonempty_iff_eq_empty] at hA'B'
      have hA'B_ne : (A' ∩ B).Nonempty := by
        by_contra he; rw [Finset.not_nonempty_iff_eq_empty] at he
        have hsub : A' ⊆ T := fun z hz => by
          by_contra hzT
          by_cases hzB : z ∈ B
          · exact Finset.notMem_empty z (he ▸ Finset.mem_inter.mpr ⟨hz, hzB⟩)
          · have hzB' : z ∈ B' := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hzB, hzT]⟩
            exact Finset.notMem_empty z (hA'B' ▸ Finset.mem_inter.mpr ⟨hz, hzB'⟩)
        have := (hA'_card.trans (Finset.card_le_card hsub)); omega
      have hAB'_ne : (A ∩ B').Nonempty := by
        by_contra he; rw [Finset.not_nonempty_iff_eq_empty] at he
        have hsub : B' ⊆ S := fun z hz => by
          by_contra hzS
          by_cases hzA : z ∈ A
          · exact Finset.notMem_empty z (he ▸ Finset.mem_inter.mpr ⟨hzA, hz⟩)
          · have hzA' : z ∈ A' := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hzA, hzS]⟩
            exact Finset.notMem_empty z (hA'B' ▸ Finset.mem_inter.mpr ⟨hzA', hz⟩)
        have := (hB'_card.trans (Finset.card_le_card hsub)); omega
      have hA'B_lt : (A' ∩ B).card < a := by
        rw [← hBcard]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.inter_subset_right, fun heq => ?_⟩
        have hwA' : w ∈ A' := (Finset.mem_inter.mp (heq ▸ hwB)).1
        simp only [A', Finset.mem_sdiff, Finset.mem_union, not_or] at hwA'
        exact hwA'.2.1 hwA
      let W1 := (S ∩ (B ∪ T)) ∪ (T ∩ A')
      let W2 := (S ∩ (B' ∪ T)) ∪ (T ∩ A)
      have hsum : W1.card + W2.card ≤ 2 * κ := by
        have hW1_sub : W1 ⊆ (S ∩ B) ∪ (S ∩ T) ∪ (T ∩ A') := by
          intro z hz; simp only [W1, Finset.mem_union, Finset.mem_inter] at hz ⊢; tauto
        have hW2_sub : W2 ⊆ (S ∩ B') ∪ (S ∩ T) ∪ (T ∩ A) := by
          intro z hz; simp only [W2, Finset.mem_union, Finset.mem_inter] at hz ⊢; tauto
        have h1 : W1.card ≤ (S ∩ B).card + (S ∩ T).card + (T ∩ A').card :=
          (Finset.card_le_card hW1_sub).trans ((Finset.card_union_le _ _).trans (by gcongr; exact Finset.card_union_le _ _))
        have h2 : W2.card ≤ (S ∩ B').card + (S ∩ T).card + (T ∩ A).card :=
          (Finset.card_le_card hW2_sub).trans ((Finset.card_union_le _ _).trans (by gcongr; exact Finset.card_union_le _ _))
        have hS_part : (S ∩ B).card + (S ∩ T).card + (S ∩ B').card ≤ S.card := by
          have hd1 : Disjoint (S ∩ B) (S ∩ T) := Finset.disjoint_left.mpr fun z h1 h2 =>
            Finset.disjoint_left.mp hB_disj_T (Finset.mem_inter.mp h1).2 (Finset.mem_inter.mp h2).2
          have hd2 : Disjoint ((S ∩ B) ∪ (S ∩ T)) (S ∩ B') := Finset.disjoint_left.mpr fun z h1 h2 => by
            have hzB' := (Finset.mem_inter.mp h2).2
            simp only [B', Finset.mem_sdiff, Finset.mem_union, not_or] at hzB'
            rcases Finset.mem_union.mp h1 with h | h
            · exact hzB'.2.1 (Finset.mem_inter.mp h).2
            · exact hzB'.2.2 (Finset.mem_inter.mp h).2
          rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2]
          apply Finset.card_le_card; intro z hz; simp only [Finset.mem_union, Finset.mem_inter] at hz; tauto
        have hT_part : (T ∩ A').card + (S ∩ T).card + (T ∩ A).card ≤ T.card := by
          have hST : S ∩ T = T ∩ S := Finset.inter_comm S T
          rw [hST]
          have hd1 : Disjoint (T ∩ A') (T ∩ S) := Finset.disjoint_left.mpr fun z h1 h2 => by
            have hzA' := (Finset.mem_inter.mp h1).2
            simp only [A', Finset.mem_sdiff, Finset.mem_union, not_or] at hzA'
            exact hzA'.2.2 (Finset.mem_inter.mp h2).2
          have hd2 : Disjoint ((T ∩ A') ∪ (T ∩ S)) (T ∩ A) := Finset.disjoint_left.mpr fun z h1 h2 => by
            have hzA := (Finset.mem_inter.mp h2).2
            rcases Finset.mem_union.mp h1 with h | h
            · have hzA' := (Finset.mem_inter.mp h).2
              simp only [A', Finset.mem_sdiff, Finset.mem_union, not_or] at hzA'
              exact hzA'.2.1 hzA
            · exact Finset.disjoint_left.mp hA_disj_S hzA (Finset.mem_inter.mp h).2
          rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2]
          apply Finset.card_le_card; intro z hz; simp only [Finset.mem_union, Finset.mem_inter] at hz; tauto
        omega
      exact hsplit_contra (A' ∩ B) (A ∩ B') W1 W2 hA'B_ne hAB'_ne
        (Finset.disjoint_left.mpr fun z h1 h2 => by
          simp only [W1, A', Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, not_or] at h1 h2
          rcases h2 with ⟨hzS, _⟩ | ⟨hzT, _⟩
          · exact h1.1.2.2 hzS
          · exact Finset.disjoint_left.mp hB_disj_T h1.2 hzT)
        (Finset.disjoint_left.mpr fun z h1 h2 => by
          simp only [W1, A', B', Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, not_or] at h1 h2
          tauto)
        (Finset.disjoint_left.mpr fun z h1 h2 => by
          simp only [A', Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union, not_or] at h1 h2
          exact h1.1.2.1 h2.1)
        (Finset.disjoint_left.mpr fun z h1 h2 => by
          simp only [W2, B', Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, not_or] at h1 h2
          rcases h2 with ⟨hzS, _⟩ | ⟨hzT, _⟩
          · exact Finset.disjoint_left.mp hA_disj_S h1.1 hzS
          · exact h1.2.2.2 hzT)
        (Finset.disjoint_left.mpr fun z h1 h2 => by
          simp only [W2, A', B', Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, not_or] at h1 h2
          tauto)
        (fun y hy z hyz => by
          obtain ⟨hyA', hyB⟩ := Finset.mem_inter.mp hy
          have h1 := hA'_closed y hyA' z hyz
          have h2 := hB_closed y hyB z hyz
          simp only [W1, Finset.mem_union, Finset.mem_inter] at h1 h2 ⊢; tauto)
        (fun y hy z hyz => by
          obtain ⟨hyA, hyB'⟩ := Finset.mem_inter.mp hy
          have h1 := hA_closed y hyA z hyz
          have h2 := hB'_closed y hyB' z hyz
          simp only [W2, Finset.mem_union, Finset.mem_inter] at h1 h2 ⊢; tauto)
        hsum hA'B_lt
  -- Step 2: Now A ∩ B = ∅ and x ∈ B ∩ S. Since a > κ, A' ∩ B ≠ ∅ and A ∩ B' ≠ ∅, contradiction!
  have hA'B_ne : (A' ∩ B).Nonempty := by
    by_contra he; rw [Finset.not_nonempty_iff_eq_empty] at he
    have hsub : B ⊆ S := fun z hz => by
      by_contra hzS
      have hzA : z ∉ A := Finset.disjoint_right.mp hAB_empty hz
      have hzA' : z ∈ A' := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hzA, hzS]⟩
      exact Finset.notMem_empty z (he ▸ Finset.mem_inter.mpr ⟨hzA', hz⟩)
    have := Finset.card_le_card hsub; omega
  have hAB'_ne : (A ∩ B').Nonempty := by
    by_contra he; rw [Finset.not_nonempty_iff_eq_empty] at he
    have hsub : A ⊆ T := fun z hz => by
      by_contra hzT
      have hzB : z ∉ B := Finset.disjoint_left.mp hAB_empty hz
      have hzB' : z ∈ B' := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hzB, hzT]⟩
      exact Finset.notMem_empty z (he ▸ Finset.mem_inter.mpr ⟨hz, hzB'⟩)
    have := Finset.card_le_card hsub; omega
  have hA'B_lt : (A' ∩ B).card < a := by
    rw [← hBcard]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.inter_subset_right, fun heq => ?_⟩
    have hxA' : x ∈ A' := (Finset.mem_inter.mp (heq ▸ hxB)).1
    simp only [A', Finset.mem_sdiff, Finset.mem_union, not_or] at hxA'
    exact hxA'.2.2 hxS
  let W1 := (S ∩ (B ∪ T)) ∪ (T ∩ A')
  let W2 := (S ∩ (B' ∪ T)) ∪ (T ∩ A)
  have hsum : W1.card + W2.card ≤ 2 * κ := by
    have hW1_sub : W1 ⊆ (S ∩ B) ∪ (S ∩ T) ∪ (T ∩ A') := by
      intro z hz; simp only [W1, Finset.mem_union, Finset.mem_inter] at hz ⊢; tauto
    have hW2_sub : W2 ⊆ (S ∩ B') ∪ (S ∩ T) ∪ (T ∩ A) := by
      intro z hz; simp only [W2, Finset.mem_union, Finset.mem_inter] at hz ⊢; tauto
    have h1 : W1.card ≤ (S ∩ B).card + (S ∩ T).card + (T ∩ A').card :=
      (Finset.card_le_card hW1_sub).trans ((Finset.card_union_le _ _).trans (by gcongr; exact Finset.card_union_le _ _))
    have h2 : W2.card ≤ (S ∩ B').card + (S ∩ T).card + (T ∩ A).card :=
      (Finset.card_le_card hW2_sub).trans ((Finset.card_union_le _ _).trans (by gcongr; exact Finset.card_union_le _ _))
    have hS_part : (S ∩ B).card + (S ∩ T).card + (S ∩ B').card ≤ S.card := by
      have hd1 : Disjoint (S ∩ B) (S ∩ T) := Finset.disjoint_left.mpr fun z h1 h2 =>
        Finset.disjoint_left.mp hB_disj_T (Finset.mem_inter.mp h1).2 (Finset.mem_inter.mp h2).2
      have hd2 : Disjoint ((S ∩ B) ∪ (S ∩ T)) (S ∩ B') := Finset.disjoint_left.mpr fun z h1 h2 => by
        have hzB' := (Finset.mem_inter.mp h2).2
        simp only [B', Finset.mem_sdiff, Finset.mem_union, not_or] at hzB'
        rcases Finset.mem_union.mp h1 with h | h
        · exact hzB'.2.1 (Finset.mem_inter.mp h).2
        · exact hzB'.2.2 (Finset.mem_inter.mp h).2
      rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2]
      apply Finset.card_le_card; intro z hz; simp only [Finset.mem_union, Finset.mem_inter] at hz; tauto
    have hT_part : (T ∩ A').card + (S ∩ T).card + (T ∩ A).card ≤ T.card := by
      have hST : S ∩ T = T ∩ S := Finset.inter_comm S T
      rw [hST]
      have hd1 : Disjoint (T ∩ A') (T ∩ S) := Finset.disjoint_left.mpr fun z h1 h2 => by
        have hzA' := (Finset.mem_inter.mp h1).2
        simp only [A', Finset.mem_sdiff, Finset.mem_union, not_or] at hzA'
        exact hzA'.2.2 (Finset.mem_inter.mp h2).2
      have hd2 : Disjoint ((T ∩ A') ∪ (T ∩ S)) (T ∩ A) := Finset.disjoint_left.mpr fun z h1 h2 => by
        have hzA := (Finset.mem_inter.mp h2).2
        rcases Finset.mem_union.mp h1 with h | h
        · have hzA' := (Finset.mem_inter.mp h).2
          simp only [A', Finset.mem_sdiff, Finset.mem_union, not_or] at hzA'
          exact hzA'.2.1 hzA
        · exact Finset.disjoint_left.mp hA_disj_S hzA (Finset.mem_inter.mp h).2
      rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2]
      apply Finset.card_le_card; intro z hz; simp only [Finset.mem_union, Finset.mem_inter] at hz; tauto
    omega
  exact hsplit_contra (A' ∩ B) (A ∩ B') W1 W2 hA'B_ne hAB'_ne
    (Finset.disjoint_left.mpr fun z h1 h2 => by
      simp only [W1, A', Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, not_or] at h1 h2
      rcases h2 with ⟨hzS, _⟩ | ⟨hzT, _⟩
      · exact h1.1.2.2 hzS
      · exact Finset.disjoint_left.mp hB_disj_T h1.2 hzT)
    (Finset.disjoint_left.mpr fun z h1 h2 => by
      simp only [W1, A', B', Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, not_or] at h1 h2
      tauto)
    (Finset.disjoint_left.mpr fun z h1 h2 => by
      simp only [A', Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union, not_or] at h1 h2
      exact h1.1.2.1 h2.1)
    (Finset.disjoint_left.mpr fun z h1 h2 => by
      simp only [W2, B', Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, not_or] at h1 h2
      rcases h2 with ⟨hzS, _⟩ | ⟨hzT, _⟩
      · exact Finset.disjoint_left.mp hA_disj_S h1.1 hzS
      · exact h1.2.2.2 hzT)
    (Finset.disjoint_left.mpr fun z h1 h2 => by
      simp only [W2, A', B', Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, not_or] at h1 h2
      tauto)
    (fun y hy z hyz => by
      obtain ⟨hyA', hyB⟩ := Finset.mem_inter.mp hy
      have h1 := hA'_closed y hyA' z hyz
      have h2 := hB_closed y hyB z hyz
      simp only [W1, Finset.mem_union, Finset.mem_inter] at h1 h2 ⊢; tauto)
    (fun y hy z hyz => by
      obtain ⟨hyA, hyB'⟩ := Finset.mem_inter.mp hy
      have h1 := hA_closed y hyA z hyz
      have h2 := hB'_closed y hyB' z hyz
      simp only [W2, Finset.mem_union, Finset.mem_inter] at h1 h2 ⊢; tauto)
    hsum hA'B_lt

end Connectivity


section Menger2

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Shortest path avoiding S between two disjoint Finsets X and Y: interior is disjoint from X ∪ Y. -/
lemma exists_minimal_path_between {S X Y : Finset V}
    (hXY : Disjoint X Y) (hXS : Disjoint X S) (hYS : Disjoint Y S)
    (hex : ∃ a ∈ X, ∃ b ∈ Y, ReachAvoiding G S a b) :
    ∃ (a b : V) (p : G.Walk a b),
      a ∈ X ∧ b ∈ Y ∧ p.IsPath ∧ 1 ≤ p.length ∧
      (∀ w ∈ p.support, w ∉ S) ∧
      (∀ w ∈ p.support, w ≠ a → w ≠ b → w ∉ X ∧ w ∉ Y) := by
  classical
  have hex_len : ∃ l : ℕ, ∃ (a b : V) (p : G.Walk a b),
      a ∈ X ∧ b ∈ Y ∧ (∀ w ∈ p.support, w ∉ S) ∧ p.length = l := by
    obtain ⟨a, ha, b, hb, p, hp⟩ := hex
    exact ⟨p.length, a, b, p, ha, hb, hp, rfl⟩
  let m := Nat.find hex_len
  obtain ⟨a, b, p, haX, hbY, hpS, hplen⟩ := Nat.find_spec hex_len
  have hmin : ∀ (a' b' : V) (q : G.Walk a' b'), a' ∈ X → b' ∈ Y → (∀ w ∈ q.support, w ∉ S) → m ≤ q.length :=
    fun a' b' q ha' hb' hqS => Nat.find_min' hex_len ⟨a', b', q, ha', hb', hqS, rfl⟩
  have hab : a ≠ b := fun h => Finset.disjoint_left.mp hXY haX (h ▸ hbY)
  let q := p.bypass
  have hqS : ∀ w ∈ q.support, w ∉ S := fun w hw => hpS w (Walk.support_bypass_subset p hw)
  have hqlen : q.length = m := by
    have hle : q.length ≤ p.length := p.length_bypass_le
    have hge : m ≤ q.length := hmin a b q haX hbY hqS
    omega
  have hpos : 1 ≤ q.length := by
    cases hq : q with
    | nil => exact absurd rfl hab
    | cons _ _ => simp
  have hint : ∀ w ∈ q.support, w ≠ a → w ≠ b → w ∉ X ∧ w ∉ Y := by
    intro w hw hwa hwb
    constructor
    · intro hwX
      let r := q.dropUntil w hw
      have hr_lt : r.length < q.length := Walk.length_dropUntil_lt_length hw hwa
      have hrS : ∀ z ∈ r.support, z ∉ S := fun z hz => hqS z (Walk.support_dropUntil_subset q hw hz)
      have := hmin w b r hwX hbY hrS
      omega
    · intro hwY
      let r := q.takeUntil w hw
      have hr_lt : r.length < q.length := Walk.length_takeUntil_lt_length hw hwb
      have hrS : ∀ z ∈ r.support, z ∉ S := fun z hz => hqS z (Walk.support_takeUntil_subset q hw hz)
      have := hmin a w r haX hwY hrS
      omega
  exact ⟨a, b, q, haX, hbY, p.bypass_isPath, hpos, hqS, hint⟩

/-- Trim a path from a ∈ A to b ∈ B (with A, B disjoint) to a subpath whose interior is disjoint from A ∪ B. -/
lemma trim_path_between {A B : Finset V} (hAB : Disjoint A B)
    {a b : V} (p : G.Walk a b) (ha : a ∈ A) (hb : b ∈ B) :
    ∃ (a' b' : V) (q : G.Walk a' b'),
      a' ∈ A ∧ b' ∈ B ∧ q.IsPath ∧ 1 ≤ q.length ∧
      walkVerts G q ⊆ walkVerts G p ∧
      (∀ w ∈ q.support, w ≠ a' → w ≠ b' → w ∉ A ∧ w ∉ B) := by
  classical
  let S : Finset V := Finset.univ \ walkVerts G p
  have h1 : ∃ x ∈ A ∩ walkVerts G p, ∃ y ∈ B ∩ walkVerts G p, ReachAvoiding G S x y :=
    ⟨a, Finset.mem_inter.mpr ⟨ha, (mem_walkVerts G).mpr (Walk.start_mem_support p)⟩,
     b, Finset.mem_inter.mpr ⟨hb, (mem_walkVerts G).mpr (Walk.end_mem_support p)⟩,
     p, fun w hw hS => (Finset.mem_sdiff.mp hS).2 ((mem_walkVerts G).mpr hw)⟩
  obtain ⟨a', b', q, ha', hb', hq_path, hq_pos, hqS, hq_int⟩ :=
    exists_minimal_path_between G
      (hAB.mono Finset.inter_subset_left Finset.inter_subset_left)
      (Finset.disjoint_left.mpr fun z hz hS => (Finset.mem_sdiff.mp hS).2 (Finset.mem_inter.mp hz).2)
      (Finset.disjoint_left.mpr fun z hz hS => (Finset.mem_sdiff.mp hS).2 (Finset.mem_inter.mp hz).2)
      h1
  have hsub : walkVerts G q ⊆ walkVerts G p := fun z hz => by
    by_contra hnot
    exact hqS z ((mem_walkVerts G).mp hz) (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
  refine ⟨a', b', q, (Finset.mem_inter.mp ha').1, (Finset.mem_inter.mp hb').1, hq_path, hq_pos, hsub, ?_⟩
  intro w hw hwa hwb
  have hwP : w ∈ walkVerts G p := hsub ((mem_walkVerts G).mpr hw)
  have hi := hq_int w hw hwa hwb
  exact ⟨fun hA => hi.1 (Finset.mem_inter.mpr ⟨hA, hwP⟩), fun hB => hi.2 (Finset.mem_inter.mpr ⟨hB, hwP⟩)⟩

/-- Helper: trace a functional, injective directed relation on a finite type from a source (no in-edge)
until a sink (no out-edge). -/
lemma trace_functional_rel {α : Type} [Fintype α] [DecidableEq α] [Inhabited α]
    (E : α → α → Prop) [DecidableRel E]
    (hout_uniq : ∀ x y1 y2, E x y1 → E x y2 → y1 = y2)
    (hin_uniq : ∀ x1 x2 y, E x1 y → E x2 y → x1 = x2)
    (s : α) (hno_in : ∀ x, ¬ E x s) :
    ∃ L : List α, L ≠ [] ∧ L.Nodup ∧ L.head! = s ∧
      (∀ i (hi : i + 1 < L.length), E L[i] L[i + 1]) ∧
      (∀ y, ¬ E L.getLast! y) := by
  classical
  -- Build maximal prefix of length ≤ Fintype.card α by induction on remaining budget
  have hbuild : ∀ (k : ℕ) (L : List α),
      L ≠ [] → L.Nodup → L.head! = s →
      (∀ i (hi : i + 1 < L.length), E L[i] L[i + 1]) →
      Fintype.card α - L.length ≤ k →
      ∃ L' : List α, L' ≠ [] ∧ L'.Nodup ∧ L'.head! = s ∧
        (∀ i (hi : i + 1 < L'.length), E L'[i] L'[i + 1]) ∧
        (∀ y, ¬ E L'.getLast! y) := by
    intro k
    induction k with
    | zero =>
      intro L hLne hLnd hLh hLadj hrem
      refine ⟨L, hLne, hLnd, hLh, hLadj, fun y hy => ?_⟩
      -- Since L.length = Fintype.card α and L.Nodup, y ∈ L!
      have hy_mem : y ∈ L := by
        have hlen : L.toFinset.card = Fintype.card α := by
          rw [List.toFinset_card_of_nodup hLnd]
          have hle := (List.toFinset_card_of_nodup hLnd) ▸ Finset.card_le_univ L.toFinset
          omega
        have huniv : L.toFinset = Finset.univ := Finset.eq_univ_of_card _ hlen
        exact List.mem_toFinset.mp (huniv ▸ Finset.mem_univ y)
      obtain ⟨idx, hidx, hyeq⟩ := List.mem_iff_getElem.mp hy_mem
      cases idx with
      | zero =>
        have hys : y = s := by
          have h0 : L[0]'(List.length_pos_of_ne_nil hLne) = L.head! := by
            cases L with | nil => exact absurd rfl hLne | cons _ _ => rfl
          exact hyeq.symm.trans (h0.trans hLh)
        exact hno_in _ (hys ▸ hy)
      | succ j =>
        have hprev : E L[j] y := hyeq ▸ hLadj j hidx
        have hlast_eq : L.getLast! = L[L.length - 1]'(by cases L with | nil => exact absurd rfl hLne | cons _ _ => simp) := by
          have hpos : 0 < L.length := List.length_pos_of_ne_nil hLne
          rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
        have heq_idx : L[j]'(by omega) = L[L.length - 1]'(by omega) := hin_uniq _ _ y hprev (hlast_eq ▸ hy)
        have := (List.Nodup.getElem_inj_iff hLnd).mp heq_idx
        omega
    | succ k ih =>
      intro L hLne hLnd hLh hLadj hrem
      by_cases hex : ∃ y, E L.getLast! y
      · obtain ⟨y, hy⟩ := hex
        have hy_not_mem : y ∉ L := by
          intro hmem
          obtain ⟨idx, hidx, hyeq⟩ := List.mem_iff_getElem.mp hmem
          cases idx with
          | zero =>
            have hys : y = s := by
              have h0 : L[0]'(List.length_pos_of_ne_nil hLne) = L.head! := by
                cases L with | nil => exact absurd rfl hLne | cons _ _ => rfl
              exact hyeq.symm.trans (h0.trans hLh)
            exact hno_in _ (hys ▸ hy)
          | succ j =>
            have hprev : E L[j] y := hyeq ▸ hLadj j hidx
            have hlast_eq : L.getLast! = L[L.length - 1]'(by cases L with | nil => exact absurd rfl hLne | cons _ _ => simp) := by
              have hpos : 0 < L.length := List.length_pos_of_ne_nil hLne
              rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
            have heq_idx : L[j]'(by omega) = L[L.length - 1]'(by omega) := hin_uniq _ _ y hprev (hlast_eq ▸ hy)
            have := (List.Nodup.getElem_inj_iff hLnd).mp heq_idx
            omega
        let L1 := L ++ [y]
        have hL1ne : L1 ≠ [] := by simp [L1]
        have hL1nd : L1.Nodup := List.nodup_append.mpr ⟨hLnd, List.nodup_singleton y, fun a ha b hb => by
          rw [List.mem_singleton] at hb; subst hb; intro h; exact hy_not_mem (h ▸ ha)⟩
        have hL1h : L1.head! = s := by
          cases hL : L with
          | nil => exact absurd hL hLne
          | cons a as => simp [L1, hL, ← hLh]
        have hL1adj : ∀ i (hi : i + 1 < L1.length), E L1[i] L1[i + 1] := by
          intro i hi
          have hlen1 : L1.length = L.length + 1 := by simp [L1]
          by_cases hlt : i + 1 < L.length
          · simp only [L1, List.getElem_append_left (by omega : i < L.length), List.getElem_append_left hlt]
            exact hLadj i hlt
          · have hieq : i = L.length - 1 := by omega
            have hlast_eq : L.getLast! = L[L.length - 1]'(by cases L with | nil => exact absurd rfl hLne | cons _ _ => simp) := by
              have hpos : 0 < L.length := List.length_pos_of_ne_nil hLne
              rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
            have he1 : L1[i] = L.getLast! := by
              rw [hlast_eq]; simp only [L1, List.getElem_append_left (by omega : i < L.length)]; congr 1
            have he2 : L1[i + 1] = y := by
              simp only [L1, List.getElem_append_right (by omega : L.length ≤ i + 1)]
              have : i + 1 - L.length = 0 := by omega
              simp [this]
            rw [he1, he2]; exact hy
        have hrem1 : Fintype.card α - L1.length ≤ k := by simp [L1]; omega
        exact ih L1 hL1ne hL1nd hL1h hL1adj hrem1
      · push Not at hex
        exact ⟨L, hLne, hLnd, hLh, hLadj, hex⟩
  exact hbuild (Fintype.card α) [s] (List.cons_ne_nil _ _) (List.nodup_singleton s) rfl
    (fun i hi => by simp at hi) (by omega)

/-- Two traces of an injective relation from distinct sources (each with no in-edge) are disjoint! -/
lemma trace_disjoint {α : Type} [Inhabited α] (E : α → α → Prop)
    (hin_uniq : ∀ x1 x2 y, E x1 y → E x2 y → x1 = x2)
    {s1 s2 : α} (hs12 : s1 ≠ s2)
    (hno1 : ∀ x, ¬ E x s1) (hno2 : ∀ x, ¬ E x s2)
    {L1 L2 : List α} (h1ne : L1 ≠ []) (h2ne : L2 ≠ [])
    (h1h : L1.head! = s1) (h2h : L2.head! = s2)
    (h1adj : ∀ i (hi : i + 1 < L1.length), E L1[i] L1[i + 1])
    (h2adj : ∀ i (hi : i + 1 < L2.length), E L2[i] L2[i + 1]) :
    L1.Disjoint L2 := by
  rw [List.disjoint_left]
  intro z hz1 hz2
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz1
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hz2
  have haux : ∀ n i j (hi : i < L1.length) (hj : j < L2.length), i + j = n → L1[i] ≠ L2[j] := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro i j hi hj hsum heq'
      cases i with
      | zero =>
        cases j with
        | zero =>
          have h10 : L1[0] = s1 := by rw [← h1h]; cases L1 with | nil => exact absurd rfl h1ne | cons _ _ => rfl
          have h20 : L2[0] = s2 := by rw [← h2h]; cases L2 with | nil => exact absurd rfl h2ne | cons _ _ => rfl
          rw [h10, h20] at heq'; exact hs12 heq'
        | succ j' =>
          have h10 : L1[0] = s1 := by rw [← h1h]; cases L1 with | nil => exact absurd rfl h1ne | cons _ _ => rfl
          have hE := h2adj j' hj
          rw [← heq', h10] at hE
          exact hno1 L2[j'] hE
      | succ i' =>
        cases j with
        | zero =>
          have h20 : L2[0] = s2 := by rw [← h2h]; cases L2 with | nil => exact absurd rfl h2ne | cons _ _ => rfl
          have hE := h1adj i' hi
          rw [heq', h20] at hE
          exact hno2 L1[i'] hE
        | succ j' =>
          have hprev := hin_uniq L1[i'] L2[j'] L1[i' + 1] (h1adj i' hi) (heq' ▸ h2adj j' hj)
          exact ih (i' + j') (by omega) i' j' (by omega) (by omega) rfl hprev
  exact haux (i + j) i j hi hj rfl heq.symm

/-- Convert a valid D-trace from (a, false) to (b, true) into a simple path G.Walk a b whose support
vertices are the first components of the trace! -/
lemma walk_of_D_trace [Inhabited V] {a b : V} (L : List (V × Bool))
    (hLne : L ≠ []) (hLnd : L.Nodup)
    (hLh : L.head! = (a, false)) (hLl : L.getLast! = (b, true))
    (hLadj : ∀ i (hi : i + 1 < L.length),
      ((L[i].2 = false ∧ L[i + 1].2 = true ∧ L[i].1 = L[i + 1].1) ∨
       (L[i].2 = true ∧ L[i + 1].2 = false ∧ G.Adj L[i].1 L[i + 1].1))) :
    ∃ p : G.Walk a b, p.IsPath ∧ ∀ w ∈ p.support, (w, false) ∈ L ∧ (w, true) ∈ L := by
  -- Induction on L.length
  have hbuild : ∀ (m : ℕ) (L : List (V × Bool)) (a : V),
      L.length = m → L ≠ [] → L.Nodup → L.head! = (a, false) → L.getLast! = (b, true) →
      (∀ i (hi : i + 1 < L.length),
        ((L[i].2 = false ∧ L[i + 1].2 = true ∧ L[i].1 = L[i + 1].1) ∨
         (L[i].2 = true ∧ L[i + 1].2 = false ∧ G.Adj L[i].1 L[i + 1].1))) →
      ∃ p : G.Walk a b, p.IsPath ∧ ∀ w ∈ p.support, (w, false) ∈ L ∧ (w, true) ∈ L := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro L a hLm hLne hLnd hLh hLl hLadj
      cases L with
      | nil => exact absurd rfl hLne
      | cons x1 xs =>
        change x1 = (a, false) at hLh
        subst hLh
        cases xs with
        | nil =>
          change (a, false) = (b, true) at hLl
          exact absurd (congrArg Prod.snd hLl) Bool.false_ne_true
        | cons x2 xs' =>
          have h01 := hLadj 0 (by simp)
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h01
          rcases h01 with ⟨_, hx2t, hx2eq⟩ | ⟨hft, _, _⟩
          · have hx2 : x2 = (a, true) := Prod.ext hx2eq.symm hx2t
            subst hx2
            cases xs' with
            | nil =>
              change (a, true) = (b, true) at hLl
              have hab : a = b := congrArg Prod.fst hLl
              subst hab
              exact ⟨Walk.nil, Walk.IsPath.nil, fun w hw => by
                simp only [Walk.support_nil, List.mem_singleton] at hw; subst hw; simp⟩
            | cons x3 xs'' =>
              have h12 := hLadj 1 (by simp)
              simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h12
              rcases h12 with ⟨hft, _, _⟩ | ⟨_, hx3f, hadj⟩
              · exact absurd hft Bool.false_ne_true.symm
              · have hx3 : x3 = (x3.1, false) := Prod.ext rfl hx3f
                let L' := x3 :: xs''
                have hL'nd : L'.Nodup := ((List.nodup_cons.mp hLnd).2 |> List.nodup_cons.mp).2
                have hL'h : L'.head! = (x3.1, false) := by simp [L', ← hx3]
                have hL'l : L'.getLast! = (b, true) := by exact hLl
                have hL'adj : ∀ i (hi : i + 1 < L'.length),
                    ((L'[i].2 = false ∧ L'[i + 1].2 = true ∧ L'[i].1 = L'[i + 1].1) ∨
                     (L'[i].2 = true ∧ L'[i + 1].2 = false ∧ G.Adj L'[i].1 L'[i + 1].1)) := fun i hi =>
                  hLadj (i + 2) (by simp [L'] at hi ⊢; omega)
                obtain ⟨q, hq_path, hq_mem⟩ := ih L'.length (by simp [L'] at hLm ⊢; omega) L' x3.1 rfl
                  (List.cons_ne_nil _ _) hL'nd hL'h hL'l hL'adj
                have ha_not_q : a ∉ q.support := fun h => by
                  have ha_in_L' : (a, false) ∈ L' := (hq_mem a h).1
                  have hnot := (List.nodup_cons.mp hLnd).1
                  exact hnot (List.mem_cons_of_mem _ ha_in_L')
                refine ⟨Walk.cons hadj q, Walk.IsPath.cons hq_path ha_not_q, fun w hw => ?_⟩
                simp only [Walk.support_cons, List.mem_cons] at hw
                rcases hw with rfl | hwq
                · exact ⟨by simp, by simp⟩
                · have hm := hq_mem w hwq
                  exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm.1),
                         List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm.2)⟩
          · exact absurd hft Bool.false_ne_true
  exact hbuild L.length L a rfl hLne hLnd hLh hLl hLadj

set_option maxHeartbeats 1200000 in
/-- 2-Path Menger Lemma: in a 2-connected graph, between any two disjoint sets A, B of size ≥ 2,
there exist two vertex-disjoint simple paths from A to B whose interiors are disjoint from A ∪ B. -/
lemma two_disjoint_paths_of_no_cut_vertex
    (hconn : G.Connected) (h2conn : ∀ x : V, ¬ IsSeparating G {x})
    {A B : Finset V} (hAB : Disjoint A B) (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card) :
    ∃ (a1 a2 b1 b2 : V) (p1 : G.Walk a1 b1) (p2 : G.Walk a2 b2),
      a1 ∈ A ∧ a2 ∈ A ∧ a1 ≠ a2 ∧ b1 ∈ B ∧ b2 ∈ B ∧ b1 ≠ b2 ∧
      p1.IsPath ∧ p2.IsPath ∧ 1 ≤ p1.length ∧ 1 ≤ p2.length ∧
      Disjoint (walkVerts G p1) (walkVerts G p2) ∧
      (∀ w ∈ p1.support, w ≠ a1 → w ≠ b1 → w ∉ A ∧ w ∉ B) ∧
      (∀ w ∈ p2.support, w ≠ a2 → w ≠ b2 → w ∉ A ∧ w ∉ B) := by
  classical
  -- Step 1: Find one minimal path P from v0 ∈ A to vr ∈ B
  obtain ⟨a0, ha0⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
  letI : Inhabited V := ⟨a0⟩
  obtain ⟨b0, hb0⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
  obtain ⟨v0, vr, P, hv0A, hvrB, hP_path, hP_pos, _, hP_int⟩ :=
    exists_minimal_path_between G hAB (Finset.disjoint_empty_right A) (Finset.disjoint_empty_right B)
      ⟨a0, ha0, b0, hb0, by obtain ⟨w⟩ := hconn a0 b0; exact ⟨w, fun _ _ => by simp⟩⟩
  set r := P.length
  let vp (i : ℕ) : V := P.getVert i
  have hvp0 : vp 0 = v0 := Walk.getVert_zero P
  have hvpr : vp r = vr := Walk.getVert_length P
  have hvp_inj : ∀ i j : ℕ, i ≤ r → j ≤ r → vp i = vp j → i = j := by
    intro i j hi hj heq
    have hnd := hP_path.support_nodup
    have hlen : P.support.length = r + 1 := P.length_support
    have hi' : i < P.support.length := by omega
    have hj' : j < P.support.length := by omega
    have hgi : P.support[i]'hi' = vp i := (Walk.getVert_eq_support_getElem P hi).symm
    have hgj : P.support[j]'hj' = vp j := (Walk.getVert_eq_support_getElem P hj).symm
    exact (List.Nodup.getElem_inj_iff hnd).mp (by rw [hgi, hgj]; exact heq)
  have hvp_adj : ∀ i : ℕ, i < r → G.Adj (vp i) (vp (i + 1)) := fun i hi =>
    P.adj_getVert_succ hi
  -- Step 2: Uniform vertex-split flow network on V × Bool
  -- Flow P runs (vp 0, false) → (vp 0, true) → (vp 1, false) → ... → (vp r, false) → (vp r, true)
  let D (x y : V × Bool) : Prop :=
    (x.2 = false ∧ y.2 = true ∧ x.1 = y.1) ∨ (x.2 = true ∧ y.2 = false ∧ G.Adj x.1 y.1)
  let F (x y : V × Bool) : Prop :=
    (∃ i : ℕ, i < r ∧ x = (vp i, true) ∧ y = (vp (i + 1), false)) ∨
    (∃ i : ℕ, i ≤ r ∧ x = (vp i, false) ∧ y = (vp i, true))
  have hF_sub_D : ∀ x y, F x y → D x y := by
    rintro x y (⟨i, hi, rfl, rfl⟩ | ⟨i, _, rfl, rfl⟩)
    · exact Or.inr ⟨rfl, rfl, hvp_adj i hi⟩
    · exact Or.inl ⟨rfl, rfl, rfl⟩
  let R (x y : V × Bool) : Prop := (D x y ∧ ¬ F x y) ∨ F y x
  let ReachR (x y : V × Bool) : Prop := Relation.ReflTransGen R x y
  let Src : Finset (V × Bool) := (A.erase v0).image (fun a => (a, false))
  let Snk : Finset (V × Bool) := (B.erase vr).image (fun b => (b, true))
  have hA_not_P : ∀ a ∈ A, a ≠ v0 → ∀ i ≤ r, a ≠ vp i := by
    intro a haA hane i hi heq; subst heq
    by_cases hi0 : i = 0
    · subst hi0; exact hane hvp0
    · by_cases hir : i = r
      · subst hir; exact Finset.disjoint_left.mp hAB (hvpr ▸ haA) hvrB
      · have hne0 : vp i ≠ v0 := fun h => hi0 (hvp_inj i 0 hi (Nat.zero_le r) (h.trans hvp0.symm))
        have hner : vp i ≠ vr := fun h => hir (hvp_inj i r hi le_rfl (h.trans hvpr.symm))
        exact (hP_int (vp i) (P.getVert_mem_support i) hne0 hner).1 haA
  have hB_not_P : ∀ b ∈ B, b ≠ vr → ∀ i ≤ r, b ≠ vp i := by
    intro b hbB hbne i hi heq; subst heq
    by_cases hi0 : i = 0
    · subst hi0; exact Finset.disjoint_left.mp hAB hv0A (hvp0 ▸ hbB)
    · by_cases hir : i = r
      · subst hir; exact hbne hvpr
      · have hne0 : vp i ≠ v0 := fun h => hi0 (hvp_inj i 0 hi (Nat.zero_le r) (h.trans hvp0.symm))
        have hner : vp i ≠ vr := fun h => hir (hvp_inj i r hi le_rfl (h.trans hvpr.symm))
        exact (hP_int (vp i) (P.getVert_mem_support i) hne0 hner).2 hbB
  -- Step 3: Prove there exists an augmenting path in R from Src to Snk
  have hex_aug : ∃ s ∈ Src, ∃ t ∈ Snk, ReachR s t := by
    by_contra hno; push Not at hno
    let X : Finset (V × Bool) := Finset.univ.filter (fun z => ∃ s ∈ Src, ReachR s z)
    have hX_closed : ∀ x ∈ X, ∀ y : V × Bool, R x y → y ∈ X := by
      intro x hx y hxy
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨s, hs, hr⟩ := hx; exact ⟨s, hs, Relation.ReflTransGen.tail hr hxy⟩
    have hSrc_sub : Src ⊆ X := fun s hs => by
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨s, hs, Relation.ReflTransGen.refl⟩
    have hSnk_disj : Disjoint Snk X := Finset.disjoint_left.mpr fun t ht htX => by
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at htX
      obtain ⟨s, hs, hr⟩ := htX; exact hno s hs t ht hr
    have hP_back_fwd : ∀ i < r, (vp (i + 1), false) ∈ X → (vp i, true) ∈ X := fun i hi h =>
      hX_closed _ h _ (Or.inr (Or.inl ⟨i, hi, rfl, rfl⟩))
    have hP_back_int : ∀ i ≤ r, (vp i, true) ∈ X → (vp i, false) ∈ X := fun i hi h =>
      hX_closed _ h _ (Or.inr (Or.inr ⟨i, hi, rfl, rfl⟩))
    have hnonP_step : ∀ u : V, (∀ i ≤ r, u ≠ vp i) → (u, false) ∈ X → (u, true) ∈ X := by
      intro u hni hu
      refine hX_closed _ hu _ (Or.inl ⟨Or.inl ⟨rfl, rfl, rfl⟩, ?_⟩)
      rintro (⟨_, _, h1, _⟩ | ⟨i, hi, h1, _⟩)
      · exact Bool.false_ne_true (congrArg Prod.snd h1)
      · exact hni i hi (congrArg Prod.fst h1)
    let XV : Finset V := Finset.univ.filter (fun u => (u, true) ∈ X)
    obtain ⟨a2, ha2A, ha2ne⟩ : ∃ a2 ∈ A, a2 ≠ v0 := Finset.exists_mem_ne (by omega : 1 < A.card) v0
    obtain ⟨b2, hb2B, hb2ne⟩ : ∃ b2 ∈ B, b2 ≠ vr := Finset.exists_mem_ne (by omega : 1 < B.card) vr
    have ha2_XV : a2 ∈ XV := by
      simp only [XV, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hnonP_step a2 (hA_not_P a2 ha2A ha2ne)
        (hSrc_sub (Finset.mem_image.mpr ⟨a2, Finset.mem_erase.mpr ⟨ha2ne, ha2A⟩, rfl⟩))
    have hb2_not_XV : b2 ∉ XV := by
      simp only [XV, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.disjoint_left.mp hSnk_disj (Finset.mem_image.mpr ⟨b2, Finset.mem_erase.mpr ⟨hb2ne, hb2B⟩, rfl⟩)
    -- Every edge u ~ w with u ∈ XV, w ∉ XV crosses along P!
    have hedge_cross : ∀ u w : V, u ∈ XV → w ∉ XV → G.Adj u w →
        (∃ i < r, u = vp i ∧ w = vp (i + 1) ∧ (vp i, true) ∈ X ∧ (vp (i + 1), false) ∉ X) ∨
        (∃ j ≤ r, w = vp j ∧ (vp j, false) ∈ X ∧ (vp j, true) ∉ X) := by
      intro u w hu hw huw
      simp only [XV, Finset.mem_filter, Finset.mem_univ, true_and] at hu hw
      by_cases hFuw : F (u, true) (w, false)
      · rcases hFuw with ⟨i, hi, h1, h2⟩ | ⟨_, _, h1, _⟩
        · have hu_eq : u = vp i := congrArg Prod.fst h1
          have hw_eq : w = vp (i + 1) := congrArg Prod.fst h2
          by_cases hwf : (vp (i + 1), false) ∈ X
          · right; exact ⟨i + 1, by omega, hw_eq, hwf, hw_eq ▸ hw⟩
          · left; exact ⟨i, hi, hu_eq, hw_eq, hu_eq ▸ hu, hwf⟩
        · exact absurd (congrArg Prod.snd h1) Bool.false_ne_true.symm
      · have hwf : (w, false) ∈ X := hX_closed _ hu _ (Or.inl ⟨Or.inr ⟨rfl, rfl, huw⟩, hFuw⟩)
        right
        by_contra hno_j; push Not at hno_j
        exact hw (hnonP_step w (fun j hj heq => (heq ▸ hw) (hno_j j hj heq (heq ▸ hwf))) hwf)
    -- Prefix property: if (vp 0, false) ∉ X, then NO node of P is in X → XV has no edges out → contradicts hconn!
    by_cases hv0f : (vp 0, false) ∈ X
    · -- Let k be the largest index ≤ r with (vp k, false) ∈ X
      let Sidx := (Finset.range (r + 1)).filter (fun i => (vp i, false) ∈ X)
      have hSne : Sidx.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos r), hv0f⟩⟩
      set k := Sidx.max' hSne
      have hk_mem : k ∈ Sidx := Finset.max'_mem Sidx hSne
      simp only [Sidx, Finset.mem_filter, Finset.mem_range] at hk_mem
      have hkr : k ≤ r := by omega
      have hkf : (vp k, false) ∈ X := hk_mem.2
      have hk_max : ∀ j, k < j → j ≤ r → (vp j, false) ∉ X := fun j hkj hjr hjX => by
        have := Finset.le_max' Sidx j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hjX⟩); omega
      -- Then {vp k} separates a2 from b2!
      have hsep : IsSeparating G {vp k} := by
        refine isSeparating_of_closed_subset G
          ⟨a2, Finset.mem_erase.mpr ⟨hA_not_P a2 ha2A ha2ne k hkr, ha2_XV⟩⟩
          (Finset.disjoint_singleton_right.mpr (Finset.notMem_erase (vp k) XV))
          ⟨b2, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, not_or]
            exact ⟨fun h => hb2_not_XV h.2, hB_not_P b2 hb2B hb2ne k hkr⟩⟩⟩ ?_
        intro u hu w huw
        obtain ⟨huk, huXV⟩ := Finset.mem_erase.mp hu
        by_cases hwXV : w ∈ XV
        · by_cases hwk : w = vp k
          · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hwk)
          · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hwXV⟩)
        · rw [Finset.mem_union]; right; rw [Finset.mem_singleton]
          rcases hedge_cross u w huXV hwXV huw with ⟨i, hir, rfl, rfl, hiX, hi1X⟩ | ⟨j, hjr, rfl, hjfX, hjtX⟩
          · -- (vp i, true) ∈ X ∧ (vp (i+1), false) ∉ X → i = k (so u = vp k, contradicting huk!)
            exfalso
            have hif : (vp i, false) ∈ X := hP_back_int i (le_of_lt hir) hiX
            have hik : i ≤ k := by by_contra hgt; exact hk_max i (by omega) (le_of_lt hir) hif
            by_cases hieq : i = k
            · exact huk (congrArg vp hieq)
            · -- i < k and (vp k, false) ∈ X → by backward induction (vp (i+1), false) ∈ X!
              apply hi1X
              have hback : ∀ d : ℕ, i + 1 + d ≤ k → (vp (i + 1 + d), false) ∈ X → (vp (i + 1), false) ∈ X := by
                intro d
                induction d with
                | zero => intro _ hX; simpa using hX
                | succ d ih =>
                  intro hle hX
                  have h1 : (vp (i + 1 + d), true) ∈ X := hP_back_fwd (i + 1 + d) (by omega) hX
                  have h2 : (vp (i + 1 + d), false) ∈ X := hP_back_int (i + 1 + d) (by omega) h1
                  exact ih (by omega) h2
              exact hback (k - (i + 1)) (by omega) (by rw [show i + 1 + (k - (i + 1)) = k by omega]; exact hkf)
          · -- (vp j, false) ∈ X ∧ (vp j, true) ∉ X → j = k!
            have hjk : j ≤ k := by by_contra hgt; exact hk_max j (by omega) hjr hjfX
            by_cases hjeq : j = k
            · rw [hjeq]
            · -- j < k and (vp k, false) ∈ X → (vp j, true) ∈ X by backward induction!
              exfalso; apply hjtX
              have hback : ∀ d : ℕ, j + 1 + d ≤ k → (vp (j + 1 + d), false) ∈ X → (vp j, true) ∈ X := by
                intro d
                induction d with
                | zero => intro _ hX; exact hP_back_fwd j (by omega) (by simpa using hX)
                | succ d ih =>
                  intro hle hX
                  have h1 : (vp (j + 1 + d), true) ∈ X := hP_back_fwd (j + 1 + d) (by omega) hX
                  have h2 : (vp (j + 1 + d), false) ∈ X := hP_back_int (j + 1 + d) (by omega) h1
                  exact ih (by omega) h2
              exact hback (k - (j + 1)) (by omega) (by rw [show j + 1 + (k - (j + 1)) = k by omega]; exact hkf)
      exact h2conn (vp k) hsep
    · -- (vp 0, false) ∉ X → no node of P is in X → XV has no edges out!
      have hno_P : ∀ i ≤ r, (vp i, false) ∉ X ∧ (vp i, true) ∉ X := by
        intro i hi
        induction i with
        | zero => exact ⟨hv0f, fun h => hv0f (hP_back_int 0 (Nat.zero_le r) h)⟩
        | succ i ih =>
          have ih' := ih (by omega)
          have h1 : (vp (i + 1), false) ∉ X := fun h => ih'.2 (hP_back_fwd i (by omega) h)
          have h2 : (vp (i + 1), true) ∉ X := fun h => h1 (hP_back_int (i + 1) hi h)
          exact ⟨h1, h2⟩
      obtain ⟨w⟩ := hconn a2 b2
      have hstay : ∀ {u v : V} (q : G.Walk u v), u ∈ XV → v ∈ XV := by
        intro u v q
        induction q with
        | nil => exact id
        | @cons u x v hux _ ih =>
          intro hu
          by_cases hx : x ∈ XV
          · exact ih hx
          · exfalso
            rcases hedge_cross u x hu hx hux with ⟨i, hi, _, _, hiX, _⟩ | ⟨j, hjr, _, hjfX, _⟩
            · exact (hno_P i (le_of_lt hi)).2 hiX
            · exact (hno_P j hjr).1 hjfX
      exact hb2_not_XV (hstay w ha2_XV)
  -- Step 4: Take a shortest augmenting path Q in R from Src to Snk
  have hex_list : ∃ n : ℕ, ∃ L : List (V × Bool),
      L.length = n ∧ L ≠ [] ∧ L.head! ∈ Src ∧ L.getLast! ∈ Snk ∧
      (∀ i (hi : i + 1 < L.length), R L[i] L[i + 1]) := by
    obtain ⟨s, hs, t, ht, hreach⟩ := hex_aug
    have hbuild : ∀ {x y : V × Bool}, ReachR x y →
        ∃ L : List (V × Bool), L ≠ [] ∧ L.head! = x ∧ L.getLast! = y ∧
          ∀ i (hi : i + 1 < L.length), R L[i] L[i + 1] := by
      intro x y hr
      induction hr using Relation.ReflTransGen.head_induction_on with
      | refl => exact ⟨[y], List.cons_ne_nil _ _, rfl, rfl, fun i hi => by simp at hi⟩
      | @head a b hab _ ih =>
        obtain ⟨L, hLne, hLh, hLl, hLadj⟩ := ih
        refine ⟨a :: L, List.cons_ne_nil _ _, rfl, ?_, ?_⟩
        · cases L with | nil => exact absurd rfl hLne | cons c cs => exact hLl
        · intro i hi
          cases i with
          | zero =>
            cases L with
            | nil => exact absurd rfl hLne
            | cons c cs => simp only [List.head!_cons] at hLh; simpa [hLh] using hab
          | succ i => exact hLadj i (by simpa using hi)
    obtain ⟨L, hne, hh, hl, hadj⟩ := hbuild hreach
    exact ⟨L.length, L, rfl, hne, hh ▸ hs, hl ▸ ht, hadj⟩
  let qlen := Nat.find hex_list
  obtain ⟨Q, hQlen, hQne, hQhead, hQlast, hQadj⟩ := Nat.find_spec hex_list
  have hQmin : ∀ L : List (V × Bool), L ≠ [] → L.head! ∈ Src → L.getLast! ∈ Snk →
      (∀ i (hi : i + 1 < L.length), R L[i] L[i + 1]) → qlen ≤ L.length :=
    fun L hne hh hl hadj => Nat.find_min' hex_list ⟨L, rfl, hne, hh, hl, hadj⟩
  have hQnodup : Q.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    simp only [Fin.mk.injEq]
    by_contra hne
    wlog hlt : i < j generalizing i j
    · exact this j hj i hi heq.symm (Ne.symm hne) (by omega)
    let Q' := Q.take (i + 1) ++ Q.drop (j + 1)
    have hQ'len : Q'.length < qlen := by
      have hlt' : Q'.length < Q.length := by
        simp only [Q', List.length_append, List.length_take, List.length_drop]; omega
      omega
    have hQ'ne : Q' ≠ [] := by
      have hpos : 0 < Q'.length := by simp only [Q', List.length_append, List.length_take, List.length_drop]; omega
      intro h; rw [h] at hpos; simp at hpos
    have hQ'head : Q'.head! ∈ Src := by
      have : Q'.head! = Q.head! := by
        cases hQ : Q with | nil => exact absurd hQ hQne | cons x xs => simp [Q', hQ]
      rw [this]; exact hQhead
    have hQ'last : Q'.getLast! ∈ Snk := by
      have : Q'.getLast! = Q.getLast! := by
        by_cases hjlast : j + 1 < Q.length
        · have hne_d : Q.drop (j + 1) ≠ [] := by intro h; have := congrArg List.length h; simp at this; omega
          rw [show Q'.getLast! = (Q.drop (j + 1)).getLast! from by
            simp only [Q', List.getLast!_eq_getLast?_getD, List.getLast?_append_of_ne_nil _ hne_d]]
          rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD, List.getLast?_drop, if_neg (by omega)]
        · have hj_eq : j = Q.length - 1 := by omega
          have hd_nil : Q.drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
          have hQ'_eq : Q' = Q.take (i + 1) := by simp [Q', hd_nil]
          rw [hQ'_eq, List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD]
          have h1 : (Q.take (i + 1)).getLast? = some (Q[i]'hi) := by
            rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left (by omega), Nat.add_sub_cancel,
              List.getElem?_take_of_lt (by omega : i < i + 1), List.getElem?_eq_getElem hi]
          have h2 : Q.getLast? = some (Q[j]'hj) := by
            rw [List.getLast?_eq_getElem?, ← hj_eq, List.getElem?_eq_getElem hj]
          have heq' : Q[i]'hi = Q[j]'hj := heq
          rw [h1, h2, heq']
      rw [this]; exact hQlast
    have hQ'adj : ∀ k (hk : k + 1 < Q'.length), R Q'[k] Q'[k + 1] := by
      intro k hk
      have hlen_t : (Q.take (i + 1)).length = i + 1 := List.length_take_of_le (by omega)
      by_cases hk1 : k + 1 < i + 1
      · have he1 : Q'[k] = Q[k]'(by omega) := by
          simp only [Q', List.getElem_append_left (by omega : k < (Q.take (i + 1)).length), List.getElem_take]
        have he2 : Q'[k + 1] = Q[k + 1]'(by omega) := by
          simp only [Q', List.getElem_append_left (by omega : k + 1 < (Q.take (i + 1)).length), List.getElem_take]
        rw [he1, he2]; exact hQadj k (by omega)
      · by_cases hk2 : k = i
        · subst k
          have he1 : Q'[i]'(Nat.lt_of_succ_lt hk) = Q[i]'hi := by
            simp only [Q', List.getElem_append_left (by omega : i < (Q.take (i + 1)).length), List.getElem_take]
          have he2 : Q'[i + 1]'hk = Q[j + 1]'(by simp [Q', hlen_t] at hk; omega) := by
            simp only [Q', List.getElem_append_right (by omega : (Q.take (i + 1)).length ≤ i + 1), hlen_t, Nat.sub_self, List.getElem_drop, Nat.add_zero]
          have heq' : Q[i]'hi = Q[j]'hj := heq
          rw [he1, he2, heq']; exact hQadj j (by simp [Q', hlen_t] at hk; omega)
        · have he1 : Q'[k] = Q[j + 1 + (k - (i + 1))]'(by simp [Q', hlen_t] at hk; omega) := by
            simp only [Q', List.getElem_append_right (by omega : (Q.take (i + 1)).length ≤ k), hlen_t, List.getElem_drop]
          have he2 : Q'[k + 1] = Q[j + 1 + (k - (i + 1)) + 1]'(by simp [Q', hlen_t] at hk; omega) := by
            simp only [Q', List.getElem_append_right (by omega : (Q.take (i + 1)).length ≤ k + 1), hlen_t, List.getElem_drop]
            congr 1; omega
          rw [he1, he2]; exact hQadj (j + 1 + (k - (i + 1))) (by simp [Q', hlen_t] at hk; omega)
    have := hQmin Q' hQ'ne hQ'head hQ'last hQ'adj
    omega
  obtain ⟨a2, ha2_mem, ha2_eq⟩ := Finset.mem_image.mp hQhead
  obtain ⟨ha2_ne, ha2A⟩ := Finset.mem_erase.mp ha2_mem
  obtain ⟨b2, hb2_mem, hb2_eq⟩ := Finset.mem_image.mp hQlast
  obtain ⟨hb2_ne, hb2B⟩ := Finset.mem_erase.mp hb2_mem
  have hQ_zero : Q[0]'(List.length_pos_of_ne_nil hQne) = (a2, false) := by
    have h0 : Q[0]'(List.length_pos_of_ne_nil hQne) = Q.head! := by
      cases Q with | nil => exact absurd rfl hQne | cons _ _ => rfl
    exact h0.trans ha2_eq.symm
  have hQ_last_elem : Q[Q.length - 1]'(by have := List.length_pos_of_ne_nil hQne; omega) = (b2, true) := by
    have hpos := List.length_pos_of_ne_nil hQne
    have hl : Q.getLast! = Q[Q.length - 1]'(by omega) := by
      rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
    exact hl.symm.trans hb2_eq.symm
  -- Step 5: Symmetric difference F' of F and Q's arcs
  let Qarc (x y : V × Bool) : Prop :=
    ∃ k : ℕ, ∃ hk : k + 1 < Q.length, Q[k] = x ∧ Q[k + 1] = y
  let F' (x y : V × Bool) : Prop := (F x y ∧ ¬ Qarc y x) ∨ (Qarc x y ∧ ¬ F y x)
  have hF'_sub_D : ∀ x y, F' x y → D x y := by
    rintro x y (⟨hFxy, _⟩ | ⟨⟨k, hk, rfl, rfl⟩, hnotF⟩)
    · exact hF_sub_D x y hFxy
    · rcases hQadj k hk with ⟨hD, _⟩ | hFyx
      · exact hD
      · exact absurd hFyx hnotF
  have hQarc_out_uniq : ∀ x y1 y2, Qarc x y1 → Qarc x y2 → y1 = y2 := by
    rintro x y1 y2 ⟨k1, hk1, h1x, rfl⟩ ⟨k2, hk2, h2x, rfl⟩
    have : k1 = k2 := (List.Nodup.getElem_inj_iff hQnodup).mp (h1x.trans h2x.symm)
    subst this; rfl
  have hQarc_in_uniq : ∀ x1 x2 y, Qarc x1 y → Qarc x2 y → x1 = x2 := by
    rintro x1 x2 y ⟨k1, hk1, rfl, h1y⟩ ⟨k2, hk2, rfl, h2y⟩
    have : k1 + 1 = k2 + 1 := (List.Nodup.getElem_inj_iff hQnodup).mp (h1y.trans h2y.symm)
    have : k1 = k2 := by omega
    subst this; rfl
  have hF_out_uniq : ∀ x y1 y2, F x y1 → F x y2 → y1 = y2 := by
    rintro x y1 y2 (⟨i1, hi1, rfl, rfl⟩ | ⟨i1, hi1, rfl, rfl⟩) (⟨i2, hi2, h2, rfl⟩ | ⟨i2, hi2, h2, rfl⟩)
    · have := hvp_inj i1 i2 (le_of_lt hi1) (le_of_lt hi2) (congrArg Prod.fst h2); subst this; rfl
    · exact absurd (congrArg Prod.snd h2) Bool.false_ne_true.symm
    · exact absurd (congrArg Prod.snd h2) Bool.false_ne_true
    · have := hvp_inj i1 i2 hi1 hi2 (congrArg Prod.fst h2); subst this; rfl
  have hF_in_uniq : ∀ x1 x2 y, F x1 y → F x2 y → x1 = x2 := by
    rintro x1 x2 y (⟨i1, hi1, rfl, rfl⟩ | ⟨i1, hi1, rfl, rfl⟩) (⟨i2, hi2, rfl, h2⟩ | ⟨i2, hi2, rfl, h2⟩)
    · have := hvp_inj (i1 + 1) (i2 + 1) (by omega) (by omega) (congrArg Prod.fst h2)
      have : i1 = i2 := by omega
      subst this; rfl
    · exact absurd (congrArg Prod.snd h2) Bool.false_ne_true
    · exact absurd (congrArg Prod.snd h2) Bool.false_ne_true.symm
    · have := hvp_inj i1 i2 hi1 hi2 (congrArg Prod.fst h2); subst this; rfl
  -- Key cancellation: if F x y1 and Qarc x y2 (with ¬ F y2 x), then Qarc y1 x!
  have hF_Qarc_out_cancel : ∀ x y1 y2, F x y1 → Qarc x y2 → ¬ F y2 x → Qarc y1 x := by
    intro x y1 y2 hF1 hQ2 hnotF2
    obtain ⟨k, hk, hkx, hky2⟩ := hQ2
    have hk_pos : 0 < k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      subst hk0
      have hx_a2 : x = (a2, false) := hkx.symm.trans hQ_zero
      subst hx_a2
      rcases hF1 with ⟨_, _, h1, _⟩ | ⟨i, hi, h1, _⟩
      · exact Bool.false_ne_true (congrArg Prod.snd h1)
      · exact hA_not_P a2 ha2A ha2_ne i hi (congrArg Prod.fst h1)
    have hRz : R (Q[k - 1]'(by omega)) x := by
      have := hQadj (k - 1) (by omega); convert this using 1; rw [← hkx]; congr 1; omega
    rcases hRz with ⟨hDzx, hnotFzx⟩ | hFxz
    · exfalso
      rcases hF1 with ⟨i, hi, rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩
      · rcases hDzx with ⟨hzf, _, hzeq⟩ | ⟨_, hft, _⟩
        · have hz_eq : Q[k - 1]'(by omega) = (vp i, false) := Prod.ext hzeq hzf
          exact hnotFzx (hz_eq.symm ▸ Or.inr ⟨i, le_of_lt hi, rfl, rfl⟩)
        · exact Bool.false_ne_true hft.symm
      · rcases hQadj k hk with ⟨hDxy2, hnotFxy2⟩ | hFy2x
        · rw [hkx, hky2] at hDxy2 hnotFxy2
          rcases hDxy2 with ⟨_, hy2t, hyeq⟩ | ⟨hft, _, _⟩
          · exact hnotFxy2 (Or.inr ⟨i, hi, rfl, Prod.ext hyeq.symm hy2t⟩)
          · exact Bool.false_ne_true hft
        · rw [hkx, hky2] at hFy2x; exact hnotF2 hFy2x
    · have hzy1 : Q[k - 1]'(by omega) = y1 := hF_out_uniq x _ y1 hFxz hF1
      exact ⟨k - 1, by omega, hzy1, by convert hkx using 1; congr 1; omega⟩
  -- Symmetric key cancellation: if F x1 y and Qarc x2 y (with ¬ F y x2), then Qarc y x1!
  have hF_Qarc_in_cancel : ∀ x1 x2 y, F x1 y → Qarc x2 y → ¬ F y x2 → Qarc y x1 := by
    intro x1 x2 y hF1 hQ2 hnotF2
    obtain ⟨k, hk, hkx2, hky⟩ := hQ2
    have hk_lt : k + 2 < Q.length := by
      by_contra hge
      have hkl : k + 1 = Q.length - 1 := by omega
      have hy_b2 : y = (b2, true) := hky.symm.trans (by
        rw [show Q[k + 1]'hk = Q[Q.length - 1]'(by omega) from by congr 1]; exact hQ_last_elem)
      subst hy_b2
      rcases hF1 with ⟨_, _, _, h2⟩ | ⟨i, hi, _, h2⟩
      · exact Bool.false_ne_true.symm (congrArg Prod.snd h2)
      · exact hB_not_P b2 hb2B hb2_ne i hi (congrArg Prod.fst h2)
    have hRz : R y (Q[k + 2]'hk_lt) := by
      have := hQadj (k + 1) hk_lt; rwa [hky] at this
    rcases hRz with ⟨hDyz, hnotFyz⟩ | hFzy
    · exfalso
      rcases hF1 with ⟨i, hi, rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩
      · rcases hDyz with ⟨_, hzt, hzeq⟩ | ⟨hft, _, _⟩
        · exact hnotFyz (Or.inr ⟨i + 1, by omega, rfl, Prod.ext hzeq.symm hzt⟩)
        · exact Bool.false_ne_true hft
      · rcases hQadj k hk with ⟨hDx2y, hnotFx2y⟩ | hFyx2
        · rw [hkx2, hky] at hDx2y hnotFx2y
          rcases hDx2y with ⟨hx2f, _, hxeq⟩ | ⟨_, hft, _⟩
          · exact hnotFx2y (Or.inr ⟨i, hi, Prod.ext hxeq hx2f, rfl⟩)
          · exact Bool.false_ne_true hft.symm
        · rw [hkx2, hky] at hFyx2; exact hnotF2 hFyx2
    · have hzx1 : Q[k + 2]'hk_lt = x1 := hF_in_uniq _ x1 y hFzy hF1
      exact ⟨k + 1, hk_lt, hky, hzx1⟩
  have hF'_out_uniq : ∀ x y1 y2, F' x y1 → F' x y2 → y1 = y2 := by
    rintro x y1 y2 (⟨hF1, hQ1⟩ | ⟨hQ1, hF1⟩) (⟨hF2, hQ2⟩ | ⟨hQ2, hF2⟩)
    · exact hF_out_uniq x y1 y2 hF1 hF2
    · exact absurd (hF_Qarc_out_cancel x y1 y2 hF1 hQ2 hF2) hQ1
    · exact absurd (hF_Qarc_out_cancel x y2 y1 hF2 hQ1 hF1) hQ2
    · exact hQarc_out_uniq x y1 y2 hQ1 hQ2
  have hF'_in_uniq : ∀ x1 x2 y, F' x1 y → F' x2 y → x1 = x2 := by
    rintro x1 x2 y (⟨hF1, hQ1⟩ | ⟨hQ1, hF1⟩) (⟨hF2, hQ2⟩ | ⟨hQ2, hF2⟩)
    · exact hF_in_uniq x1 x2 y hF1 hF2
    · exact absurd (hF_Qarc_in_cancel x1 x2 y hF1 hQ2 hF2) hQ1
    · exact absurd (hF_Qarc_in_cancel x2 x1 y hF2 hQ1 hF1) hQ2
    · exact hQarc_in_uniq x1 x2 y hQ1 hQ2
  -- No incoming F'-edges to (v0, false) or (a2, false)
  have hno_in_v0 : ∀ x, ¬ F' x (v0, false) := by
    rintro x (⟨hF, _⟩ | ⟨hQ, hnotF⟩)
    · rcases hF with ⟨i, hi, _, h2⟩ | ⟨_, _, _, h2⟩
      · have := hvp_inj (i + 1) 0 (by omega) (Nat.zero_le r) ((congrArg Prod.fst h2).symm.trans hvp0.symm); omega
      · exact Bool.false_ne_true (congrArg Prod.snd h2)
    · exact hnotF (Or.inr ⟨0, Nat.zero_le r, by rw [hvp0], by
        -- Wait: if Qarc x (v0, false) and ¬ F (v0, false) x, then Q enters (v0, false) from x,
        -- then Q leaves (v0, false)? Only D-edge out of (v0, false) is to (v0, true), which IS in F!
        -- So Q cannot leave (v0, false) at all! Wait: let's prove ¬ Qarc x (v0, false) directly!
        exfalso
        obtain ⟨k, hk, hkx, hkv0⟩ := hQ
        have hk_lt : k + 2 < Q.length := by
          by_contra hge
          have hkl : k + 1 = Q.length - 1 := by omega
          have h1 : (v0, false) = (b2, true) := hkv0.symm.trans (by
            rw [show Q[k + 1]'hk = Q[Q.length - 1]'(by omega) from by congr 1]; exact hQ_last_elem)
          exact Bool.false_ne_true (congrArg Prod.snd h1)
        rcases hQadj (k + 1) hk_lt with ⟨hD, hnotF'⟩ | hFback
        · rw [hkv0] at hD hnotF'
          rcases hD with ⟨_, hzt, hzeq⟩ | ⟨hft, _, _⟩
          · exact hnotF' (Or.inr ⟨0, Nat.zero_le r, by rw [hvp0], Prod.ext (hzeq.symm.trans hvp0.symm) hzt⟩)
          · exact Bool.false_ne_true hft
        · rw [hkv0] at hFback
          rcases hFback with ⟨i, hi, _, h2⟩ | ⟨_, _, _, h2⟩
          · have := hvp_inj (i + 1) 0 (by omega) (Nat.zero_le r) ((congrArg Prod.fst h2).symm.trans hvp0.symm); omega
          · exact Bool.false_ne_true (congrArg Prod.snd h2)⟩)
  have hno_in_a2 : ∀ x, ¬ F' x (a2, false) := by
    rintro x (⟨hF, _⟩ | ⟨⟨k, hk, _, hka2⟩, _⟩)
    · rcases hF with ⟨i, hi, _, h2⟩ | ⟨_, _, _, h2⟩
      · exact hA_not_P a2 ha2A ha2_ne (i + 1) (by omega) (congrArg Prod.fst h2)
      · exact Bool.false_ne_true (congrArg Prod.snd h2)
    · have := (List.Nodup.getElem_inj_iff hQnodup).mp (hka2.trans hQ_zero.symm)
      omega
  -- Continuation property: every node with an incoming F'-edge except (vr, true), (b2, true) has an outgoing F'-edge
  have hcont : ∀ x, (∃ w, F' w x) → x ≠ (vr, true) → x ≠ (b2, true) → ∃ y, F' x y := by
    rintro x ⟨w, hw⟩ hxvr hxb2
    rcases hw with ⟨hFwx, hnotQxw⟩ | ⟨hQwx, hnotFxw⟩
    · -- x is on P and x ≠ (vr, true), so F has an outgoing edge F x y!
      have hex_Fy : ∃ y, F x y := by
        rcases hFwx with ⟨i, hi, _, rfl⟩ | ⟨i, hi, _, rfl⟩
        · exact ⟨(vp (i + 1), true), Or.inr ⟨i + 1, by omega, rfl, rfl⟩⟩
        · by_cases hir : i < r
          · exact ⟨(vp (i + 1), false), Or.inl ⟨i, hir, rfl, rfl⟩⟩
          · exfalso; apply hxvr; rw [show i = r by omega, hvpr]
      obtain ⟨y, hFxy⟩ := hex_Fy
      by_cases hQyx : Qarc y x
      · obtain ⟨k, hk, hky, hkx⟩ := hQyx
        have hk_lt : k + 2 < Q.length := by
          by_contra hge
          have hkl : k + 1 = Q.length - 1 := by omega
          exact hxb2 (hkx.symm.trans (by
            rw [show Q[k + 1]'hk = Q[Q.length - 1]'(by omega) from by congr 1]; exact hQ_last_elem))
        refine ⟨Q[k + 2]'hk_lt, Or.inr ⟨⟨k + 1, hk_lt, hkx, rfl⟩, fun hFzx => ?_⟩⟩
        have hzw : Q[k + 2]'hk_lt = w := hF_in_uniq _ w x hFzx hFwx
        exact hnotQxw ⟨k + 1, hk_lt, hkx, hzw⟩
      · exact ⟨y, Or.inl ⟨hFxy, hQyx⟩⟩
    · obtain ⟨k, hk, hkw, hkx⟩ := hQwx
      have hk_lt : k + 2 < Q.length := by
        by_contra hge
        have hkl : k + 1 = Q.length - 1 := by omega
        exact hxb2 (hkx.symm.trans (by
          rw [show Q[k + 1]'hk = Q[Q.length - 1]'(by omega) from by congr 1]; exact hQ_last_elem))
      let z := Q[k + 2]'hk_lt
      by_cases hFzx : F z x
      · -- x has incoming F-edge F z x and x ≠ (vr, true), so F has outgoing edge F x y!
        have hex_Fy : ∃ y, F x y := by
          rcases hFzx with ⟨i, hi, _, rfl⟩ | ⟨i, hi, _, rfl⟩
          · exact ⟨(vp (i + 1), true), Or.inr ⟨i + 1, by omega, rfl, rfl⟩⟩
          · by_cases hir : i < r
            · exact ⟨(vp (i + 1), false), Or.inl ⟨i, hir, rfl, rfl⟩⟩
            · exfalso; apply hxvr; rw [show i = r by omega, hvpr]
        obtain ⟨y, hFxy⟩ := hex_Fy
        refine ⟨y, Or.inl ⟨hFxy, fun hQyx => ?_⟩⟩
        have hyw : y = w := hQarc_in_uniq y w x hQyx ⟨k, hk, hkw, hkx⟩
        exact hnotFxw (hyw ▸ hFxy)
      · exact ⟨z, Or.inr ⟨⟨k + 1, hk_lt, hkx, rfl⟩, hFzx⟩⟩
  -- Both sources (v0, false) and (a2, false) have outgoing F'-edges!
  have hout_v0 : ∃ y, F' (v0, false) y := by
    refine ⟨(v0, true), Or.inl ⟨Or.inr ⟨0, Nat.zero_le r, by rw [hvp0], by rw [hvp0]⟩, fun hQ => ?_⟩⟩
    obtain ⟨k, hk, _, hkv0⟩ := hQ
    have hk_lt : k + 2 < Q.length := by
      by_contra hge; have hkl : k + 1 = Q.length - 1 := by omega
      have h1 : (v0, false) = (b2, true) := hkv0.symm.trans (by
        rw [show Q[k + 1]'hk = Q[Q.length - 1]'(by omega) from by congr 1]; exact hQ_last_elem)
      exact Bool.false_ne_true (congrArg Prod.snd h1)
    rcases hQadj (k + 1) hk_lt with ⟨hD, hnotF'⟩ | hFback
    · rw [hkv0] at hD hnotF'
      rcases hD with ⟨_, hzt, hzeq⟩ | ⟨hft, _, _⟩
      · exact hnotF' (Or.inr ⟨0, Nat.zero_le r, by rw [hvp0], Prod.ext (hzeq.symm.trans hvp0.symm) hzt⟩)
      · exact Bool.false_ne_true hft
    · rw [hkv0] at hFback
      rcases hFback with ⟨i, hi, _, h2⟩ | ⟨_, _, _, h2⟩
      · have := hvp_inj (i + 1) 0 (by omega) (Nat.zero_le r) ((congrArg Prod.fst h2).symm.trans hvp0.symm); omega
      · exact Bool.false_ne_true (congrArg Prod.snd h2)
  have hout_a2 : ∃ y, F' (a2, false) y := by
    have hQlen2 : 1 < Q.length := by
      by_contra hle
      have h1 : Q.length = 1 := by have := List.length_pos_of_ne_nil hQne; omega
      have heq : Q.head! = Q.getLast! := by
        cases Q with | nil => exact absurd rfl hQne | cons x xs => cases xs with | nil => rfl | cons _ _ => simp at h1
      rw [← ha2_eq, ← hb2_eq] at heq
      exact Bool.false_ne_true (congrArg Prod.snd heq)
    refine ⟨Q[1], Or.inr ⟨⟨0, hQlen2, hQ_zero, rfl⟩, fun hF => ?_⟩⟩
    rcases hF with ⟨i, hi, _, h2⟩ | ⟨_, _, _, h2⟩
    · exact hA_not_P a2 ha2A ha2_ne (i + 1) (by omega) (congrArg Prod.fst h2)
    · exact Bool.false_ne_true (congrArg Prod.snd h2)
  -- Step 6: Trace F' from (v0, false) and from (a2, false)!
  obtain ⟨L1, hL1ne, hL1nd, hL1h, hL1adj, hL1end⟩ :=
    trace_functional_rel F' hF'_out_uniq hF'_in_uniq (v0, false) hno_in_v0
  obtain ⟨L2, hL2ne, hL2nd, hL2h, hL2adj, hL2end⟩ :=
    trace_functional_rel F' hF'_out_uniq hF'_in_uniq (a2, false) hno_in_a2
  have hL12_disj : L1.Disjoint L2 :=
    trace_disjoint F' hF'_in_uniq (fun h => ha2_ne (congrArg Prod.fst h).symm)
      hno_in_v0 hno_in_a2 hL1ne hL2ne hL1h hL2h hL1adj hL2adj
  -- Both traces must end in {(vr, true), (b2, true)}!
  have hL1_last : L1.getLast! = (vr, true) ∨ L1.getLast! = (b2, true) := by
    by_contra hnot; push Not at hnot
    have hL1_len2 : 1 < L1.length := by
      by_contra hle
      have hlen1 : L1.length = 1 := by have := List.length_pos_of_ne_nil hL1ne; omega
      have hlast : L1.getLast! = (v0, false) := by
        rw [← hL1h]; cases L1 with | nil => exact absurd rfl hL1ne | cons x xs => cases xs with | nil => rfl | cons _ _ => simp at hlen1
      obtain ⟨y, hy⟩ := hout_v0
      exact hL1end y (hlast ▸ hy)
    have hin : ∃ w, F' w L1.getLast! := by
      refine ⟨L1[L1.length - 2]'(by omega), ?_⟩
      have hlast_eq : L1.getLast! = L1[L1.length - 1]'(by omega) := by
        rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
      rw [hlast_eq]; convert hL1adj (L1.length - 2) (by omega) using 1; congr 1; omega
    obtain ⟨y, hy⟩ := hcont L1.getLast! hin hnot.1 hnot.2
    exact hL1end y hy
  have hL2_last : L2.getLast! = (vr, true) ∨ L2.getLast! = (b2, true) := by
    by_contra hnot; push Not at hnot
    have hL2_len2 : 1 < L2.length := by
      by_contra hle
      have hlen1 : L2.length = 1 := by have := List.length_pos_of_ne_nil hL2ne; omega
      have hlast : L2.getLast! = (a2, false) := by
        rw [← hL2h]; cases L2 with | nil => exact absurd rfl hL2ne | cons x xs => cases xs with | nil => rfl | cons _ _ => simp at hlen1
      obtain ⟨y, hy⟩ := hout_a2
      exact hL2end y (hlast ▸ hy)
    have hin : ∃ w, F' w L2.getLast! := by
      refine ⟨L2[L2.length - 2]'(by omega), ?_⟩
      have hlast_eq : L2.getLast! = L2[L2.length - 1]'(by omega) := by
        rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
      rw [hlast_eq]; convert hL2adj (L2.length - 2) (by omega) using 1; congr 1; omega
    obtain ⟨y, hy⟩ := hcont L2.getLast! hin hnot.1 hnot.2
    exact hL2end y hy
  -- Convert L1, L2 to vertex-disjoint simple paths in G, then trim to minimal A-B subpaths!
  have hL1_end_mem : L1.getLast! ∈ L1 := by
    rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?]
    have hpos : 0 < L1.length := List.length_pos_of_ne_nil hL1ne
    simp [List.getElem?_eq_getElem (by omega : L1.length - 1 < L1.length)]
  have hL2_end_mem : L2.getLast! ∈ L2 := by
    rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?]
    have hpos : 0 < L2.length := List.length_pos_of_ne_nil hL2ne
    simp [List.getElem?_eq_getElem (by omega : L2.length - 1 < L2.length)]
  have hfin : ∀ (t1 t2 : V), t1 ∈ B → t2 ∈ B →
      L1.getLast! = (t1, true) → L2.getLast! = (t2, true) →
      ∃ (a1 a2' b1 b2' : V) (p1 : G.Walk a1 b1) (p2 : G.Walk a2' b2'),
        a1 ∈ A ∧ a2' ∈ A ∧ a1 ≠ a2' ∧ b1 ∈ B ∧ b2' ∈ B ∧ b1 ≠ b2' ∧
        p1.IsPath ∧ p2.IsPath ∧ 1 ≤ p1.length ∧ 1 ≤ p2.length ∧
        Disjoint (walkVerts G p1) (walkVerts G p2) ∧
        (∀ w ∈ p1.support, w ≠ a1 → w ≠ b1 → w ∉ A ∧ w ∉ B) ∧
        (∀ w ∈ p2.support, w ≠ a2' → w ≠ b2' → w ∉ A ∧ w ∉ B) := by
    intro t1 t2 ht1B ht2B hL1t hL2t
    obtain ⟨q1, hq1_path, hq1_mem⟩ := walk_of_D_trace G L1 hL1ne hL1nd hL1h hL1t
      (fun i hi => hF'_sub_D _ _ (hL1adj i hi))
    obtain ⟨q2, hq2_path, hq2_mem⟩ := walk_of_D_trace G L2 hL2ne hL2nd hL2h hL2t
      (fun i hi => hF'_sub_D _ _ (hL2adj i hi))
    have hq_disj : Disjoint (walkVerts G q1) (walkVerts G q2) := Finset.disjoint_left.mpr fun w hw1 hw2 =>
      List.disjoint_left.mp hL12_disj (hq1_mem w ((mem_walkVerts G).mp hw1)).1 (hq2_mem w ((mem_walkVerts G).mp hw2)).1
    obtain ⟨a1, b1, p1, ha1A, hb1B, hp1_path, hp1_pos, hp1_sub, hp1_int⟩ := trim_path_between G hAB q1 hv0A ht1B
    obtain ⟨a2', b2', p2, ha2'A, hb2'B, hp2_path, hp2_pos, hp2_sub, hp2_int⟩ := trim_path_between G hAB q2 ha2A ht2B
    have hp_disj : Disjoint (walkVerts G p1) (walkVerts G p2) := hq_disj.mono hp1_sub hp2_sub
    have ha12 : a1 ≠ a2' := fun h =>
      Finset.disjoint_left.mp hp_disj ((mem_walkVerts G).mpr (Walk.start_mem_support p1))
        (h ▸ (mem_walkVerts G).mpr (Walk.start_mem_support p2))
    have hb12 : b1 ≠ b2' := fun h =>
      Finset.disjoint_left.mp hp_disj ((mem_walkVerts G).mpr (Walk.end_mem_support p1))
        (h ▸ (mem_walkVerts G).mpr (Walk.end_mem_support p2))
    exact ⟨a1, a2', b1, b2', p1, p2, ha1A, ha2'A, ha12, hb1B, hb2'B, hb12,
      hp1_path, hp2_path, hp1_pos, hp2_pos, hp_disj, hp1_int, hp2_int⟩
  rcases hL1_last with h1 | h1 <;> rcases hL2_last with h2 | h2
  · exact absurd (h1 ▸ hL1_end_mem) (fun hm => List.disjoint_left.mp hL12_disj hm (h2 ▸ hL2_end_mem))
  · exact hfin vr b2 hvrB hb2B h1 h2
  · exact hfin b2 vr hb2B hvrB h1 h2
  · exact absurd (h1 ▸ hL1_end_mem) (fun hm => List.disjoint_left.mp hL12_disj hm (h2 ▸ hL2_end_mem))

end Menger2

section CycleIntersection

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Split a cycle c at two distinct vertices x, y ∈ walkVerts G c into two internally disjoint paths
p : x → y and q : y → x with p.length + q.length = c.length. -/
lemma split_cycle {v : V} {c : G.Walk v v} (hc : c.IsCycle)
    {x y : V} (hx : x ∈ walkVerts G c) (hy : y ∈ walkVerts G c) (hxy : x ≠ y) :
    ∃ (p : G.Walk x y) (q : G.Walk y x),
      p.IsPath ∧ q.IsPath ∧ 1 ≤ p.length ∧ 1 ≤ q.length ∧
      p.length + q.length = c.length ∧
      walkVerts G p ⊆ walkVerts G c ∧ walkVerts G q ⊆ walkVerts G c ∧
      (∀ w ∈ walkVerts G c, w ∈ p.support ∨ w ∈ q.support) ∧
      (∀ w, w ∈ p.support → w ∈ q.support → w = x ∨ w = y) := by
  have hx' : x ∈ c.support := (mem_walkVerts G).mp hx
  let c' : G.Walk x x := c.rotate x hx'
  have hc' : c'.IsCycle := hc.rotate hx'
  have hlen' : c'.length = c.length := Walk.length_rotate c x hx'
  have hmem_rot : ∀ w : V, w ∈ c'.support ↔ w ∈ c.support := fun w => Walk.mem_support_rotate_iff c x hx'
  have hy' : y ∈ c'.support := (hmem_rot y).mpr ((mem_walkVerts G).mp hy)
  let p : G.Walk x y := c'.takeUntil y hy'
  let q : G.Walk y x := c'.dropUntil y hy'
  have hspec : p.append q = c' := Walk.take_spec c' hy'
  have hp_path : p.IsPath := hc'.isPath_takeUntil hy'
  have hp_pos : 1 ≤ p.length := by
    cases hp : p with
    | nil => exact absurd rfl hxy
    | cons _ _ => simp
  have hq_pos : 1 ≤ q.length := by
    cases hq : q with
    | nil => exact absurd rfl hxy.symm
    | cons _ _ => simp
  have hq_path : q.IsPath := by
    have hp_not_nil : ¬ p.Nil := fun h => hxy (Walk.Nil.eq h)
    exact Walk.IsCycle.isPath_of_append_right hp_not_nil (by rw [hspec]; exact hc')
  have hsum : p.length + q.length = c.length := by
    rw [← hlen', ← hspec, Walk.length_append]
  have hp_sub : walkVerts G p ⊆ walkVerts G c := fun w hw =>
    (mem_walkVerts G).mpr ((hmem_rot w).mp (Walk.support_takeUntil_subset c' hy' ((mem_walkVerts G).mp hw)))
  have hq_sub : walkVerts G q ⊆ walkVerts G c := fun w hw =>
    (mem_walkVerts G).mpr ((hmem_rot w).mp (Walk.support_dropUntil_subset c' hy' ((mem_walkVerts G).mp hw)))
  have hcov : ∀ w ∈ walkVerts G c, w ∈ p.support ∨ w ∈ q.support := by
    intro w hw
    have hw' : w ∈ (p.append q).support := by rw [hspec]; exact (hmem_rot w).mpr ((mem_walkVerts G).mp hw)
    exact (Walk.mem_support_append_iff p q).mp hw'
  have hinter : ∀ w, w ∈ p.support → w ∈ q.support → w = x ∨ w = y := by
    intro w hwp hwq
    by_contra hnot; push Not at hnot
    -- w ∈ p.support.tail and w ∈ q.support.tail, contradicting c'.support.tail.Nodup!
    have hwp_t : w ∈ p.support.tail := by
      have h1 := p.cons_tail_support
      rw [← h1, List.mem_cons] at hwp
      exact hwp.resolve_left hnot.1
    have hwq_t : w ∈ q.support.tail := by
      have h1 := q.cons_tail_support
      rw [← h1, List.mem_cons] at hwq
      exact hwq.resolve_left hnot.2
    have hnd : c'.support.tail.Nodup := hc'.support_nodup
    rw [← hspec, Walk.tail_support_append, List.nodup_append'] at hnd
    exact List.disjoint_left.mp hnd.2.2 hwp_t hwq_t
  exact ⟨p, q, hp_path, hq_path, hp_pos, hq_pos, hsum, hp_sub, hq_sub, hcov, hinter⟩

/-- Helper: concatenate two internally-disjoint paths p : u → v and q : v → u with at least one of length ≥ 2
to obtain a cycle of length p.length + q.length. -/
lemma cycle_of_two_paths {u v : V} (p : G.Walk u v) (q : G.Walk v u)
    (hp : p.IsPath) (hq : q.IsPath) (hlen : 1 < p.length ∨ 1 < q.length)
    (hinter : ∀ w, w ∈ p.support → w ∈ q.support → w = u ∨ w = v) :
    (p.append q).IsCycle := by
  refine hp.isCycle_append hq ?_ hlen
  rw [List.disjoint_left]
  intro w hwp hwq
  have hwp' : w ∈ p.support := List.mem_of_mem_tail hwp
  have hwq' : w ∈ q.support := List.mem_of_mem_tail hwq
  rcases hinter w hwp' hwq' with rfl | rfl
  · -- w = u ∈ p.support.tail contradicts p.support.Nodup!
    have hnd := hp.support_nodup
    rw [← p.cons_tail_support, List.nodup_cons] at hnd
    exact hnd.1 hwp
  · -- w = v ∈ q.support.tail contradicts q.support.Nodup!
    have hnd := hq.support_nodup
    rw [← q.cons_tail_support, List.nodup_cons] at hnd
    exact hnd.1 hwq

/-- Concatenate two paths p : a → b and q : b → c that share only b into a path a → c. -/
lemma isPath_append_of_inter_eq {a b c : V} (p : G.Walk a b) (q : G.Walk b c)
    (hp : p.IsPath) (hq : q.IsPath) (hinter : ∀ w, w ∈ p.support → w ∈ q.support → w = b) :
    (p.append q).IsPath := by
  apply Walk.IsPath.mk'
  rw [Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  rw [List.disjoint_left]
  intro w hwp hwq
  have hwb : w = b := hinter w hwp (List.mem_of_mem_tail hwq)
  subst hwb
  have hnd := hq.support_nodup
  rw [← q.cons_tail_support, List.nodup_cons] at hnd
  exact hnd.1 hwq

set_option maxHeartbeats 800000 in
/-- In a 3-connected graph, any two longest cycles intersect in at least 3 vertices! -/
lemma three_le_card_inter_longest_cycles
    (hconn : G.Connected)
    (h3conn : ∀ S : Finset V, S.card ≤ 2 → ¬ IsSeparating G S)
    {k : ℕ} (hmax : ∀ (v : V) (c : G.Walk v v), c.IsCycle → c.length ≤ k)
    {v1 v2 : V} {c1 : G.Walk v1 v1} {c2 : G.Walk v2 v2}
    (hc1 : c1.IsCycle) (hc2 : c2.IsCycle)
    (hl1 : c1.length = k) (hl2 : c2.length = k) :
    3 ≤ (walkVerts G c1 ∩ walkVerts G c2).card := by
  classical
  have hk3 : 3 ≤ k := by rw [← hl1]; exact hc1.three_le_length
  have hcard1 : (walkVerts G c1).card = k := (card_walkVerts_of_isCycle G hc1).trans hl1
  have hcard2 : (walkVerts G c2).card = k := (card_walkVerts_of_isCycle G hc2).trans hl2
  by_contra hlt; push Not at hlt
  have hcases : (walkVerts G c1 ∩ walkVerts G c2).card = 0 ∨
      (walkVerts G c1 ∩ walkVerts G c2).card = 1 ∨
      (walkVerts G c1 ∩ walkVerts G c2).card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · -- Case 0: c1 and c2 are vertex-disjoint → 2-path Menger gives a cycle of length ≥ k + 2 > k!
    have hdisj : Disjoint (walkVerts G c1) (walkVerts G c2) :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h0)
    obtain ⟨a1, a2, b1, b2, p1, p2, ha1, ha2, ha12, hb1, hb2, hb12,
        hp1, hp2, hp1_pos, hp2_pos, hp_disj, hp1_int, hp2_int⟩ :=
      two_disjoint_paths_of_no_cut_vertex G hconn
        (fun x => h3conn {x} (by simp)) hdisj (by omega) (by omega)
    obtain ⟨arc1a, arc1b, harc1a, harc1b, h1a_pos, h1b_pos, h1_sum, h1a_sub, h1b_sub, _, _⟩ :=
      split_cycle G hc1 ha1 ha2 ha12
    obtain ⟨arc2a, arc2b, harc2a, harc2b, h2a_pos, h2b_pos, h2_sum, h2a_sub, h2b_sub, _, _⟩ :=
      split_cycle G hc2 hb1 hb2 hb12
    -- Pick the longer arc of c1 (oriented a2 → a1) and longer arc of c2 (oriented b1 → b2)
    have hex_arc1 : ∃ A1 : G.Walk a2 a1, A1.IsPath ∧ 1 ≤ A1.length ∧ k ≤ 2 * A1.length ∧ walkVerts G A1 ⊆ walkVerts G c1 := by
      by_cases hle : arc1a.length ≤ arc1b.length
      · exact ⟨arc1b, harc1b, h1b_pos, by omega, h1b_sub⟩
      · exact ⟨arc1a.reverse, harc1a.reverse, by simp; omega, by simp; omega, fun w hw => h1a_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw))⟩
    have hex_arc2 : ∃ A2 : G.Walk b1 b2, A2.IsPath ∧ 1 ≤ A2.length ∧ k ≤ 2 * A2.length ∧ walkVerts G A2 ⊆ walkVerts G c2 := by
      by_cases hle : arc2a.length ≤ arc2b.length
      · exact ⟨arc2b.reverse, harc2b.reverse, by simp; omega, by simp; omega, fun w hw => h2b_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw))⟩
      · exact ⟨arc2a, harc2a, h2a_pos, by omega, h2a_sub⟩
    obtain ⟨A1, hA1_path, hA1_pos, hA1_len, hA1_sub⟩ := hex_arc1
    obtain ⟨A2, hA2_path, hA2_pos, hA2_len, hA2_sub⟩ := hex_arc2
    -- Form path Q1 = A1 + p1 : a2 → b1 and path Q2 = A2 + p2.reverse : b1 → a2
    have hQ1 : (A1.append p1).IsPath := isPath_append_of_inter_eq G A1 p1 hA1_path hp1 fun w hw1 hw2 => by
      by_contra hne
      have hwc1 : w ∈ walkVerts G c1 := hA1_sub ((mem_walkVerts G).mpr hw1)
      have hwb1 : w ≠ b1 := fun h => Finset.disjoint_left.mp hdisj hwc1 (h ▸ hb1)
      exact (hp1_int w hw2 hne hwb1).1 hwc1
    have hQ2 : (A2.append p2.reverse).IsPath := isPath_append_of_inter_eq G A2 p2.reverse hA2_path hp2.reverse fun w hw1 hw2 => by
      by_contra hne
      have hwc2 : w ∈ walkVerts G c2 := hA2_sub ((mem_walkVerts G).mpr hw1)
      have hw2' : w ∈ p2.support := by simpa using hw2
      have hwa2 : w ≠ a2 := fun h => Finset.disjoint_left.mp hdisj (h ▸ ha2) hwc2
      exact (hp2_int w hw2' hwa2 hne).2 hwc2
    have hC_cyc : ((A1.append p1).append (A2.append p2.reverse)).IsCycle := by
      refine cycle_of_two_paths G (A1.append p1) (A2.append p2.reverse) hQ1 hQ2
        (Or.inl (by simp; omega)) fun w hw1 hw2 => ?_
      rcases (Walk.mem_support_append_iff A1 p1).mp hw1 with hwA1 | hwp1 <;>
      rcases (Walk.mem_support_append_iff A2 p2.reverse).mp hw2 with hwA2 | hwp2
      · exfalso; exact Finset.disjoint_left.mp hdisj (hA1_sub ((mem_walkVerts G).mpr hwA1)) (hA2_sub ((mem_walkVerts G).mpr hwA2))
      · left; by_contra hne
        have hwc1 : w ∈ walkVerts G c1 := hA1_sub ((mem_walkVerts G).mpr hwA1)
        have hwp2' : w ∈ p2.support := by simpa using hwp2
        have hwb2 : w ≠ b2 := fun h => Finset.disjoint_left.mp hdisj hwc1 (h ▸ hb2)
        exact absurd hwc1 (hp2_int w hwp2' hne hwb2).1
      · right; by_contra hne
        have hwc2 : w ∈ walkVerts G c2 := hA2_sub ((mem_walkVerts G).mpr hwA2)
        have hwa1 : w ≠ a1 := fun h => Finset.disjoint_left.mp hdisj (h ▸ ha1) hwc2
        exact absurd hwc2 (hp1_int w hwp1 hwa1 hne).2
      · exfalso
        have hwp2' : w ∈ p2.support := by simpa using hwp2
        exact Finset.disjoint_left.mp hp_disj ((mem_walkVerts G).mpr hwp1) ((mem_walkVerts G).mpr hwp2')
    have hle := hmax a2 _ hC_cyc
    simp only [Walk.length_append, Walk.length_reverse] at hle
    omega
  · -- Case 1: |c1 ∩ c2| = 1, say {x}
    obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp h1
    have hx1 : x ∈ walkVerts G c1 := (Finset.mem_inter.mp (hx_eq ▸ Finset.mem_singleton_self x)).1
    have hx2 : x ∈ walkVerts G c2 := (Finset.mem_inter.mp (hx_eq ▸ Finset.mem_singleton_self x)).2
    let X1 := (walkVerts G c1).erase x
    let X2 := (walkVerts G c2).erase x
    have hX1ne : X1.Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hx1, hcard1]; omega)
    have hX2ne : X2.Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hx2, hcard2]; omega)
    have hX12_disj : Disjoint X1 X2 := Finset.disjoint_left.mpr fun w hw1 hw2 => by
      have hm : w ∈ walkVerts G c1 ∩ walkVerts G c2 := Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hw1).2, (Finset.mem_erase.mp hw2).2⟩
      rw [hx_eq, Finset.mem_singleton] at hm
      exact (Finset.mem_erase.mp hw1).1 hm
    obtain ⟨u0, hu0⟩ := hX1ne
    obtain ⟨w0, hw0⟩ := hX2ne
    have hreach : ReachAvoiding G {x} u0 w0 := by
      by_contra hnr
      exact h3conn {x} (by simp) ⟨u0, w0, by simp [(Finset.mem_erase.mp hu0).1], by simp [(Finset.mem_erase.mp hw0).1], hnr⟩
    obtain ⟨a, b, p, haX1, hbX2, hp_path, hp_pos, hp_not_x, hp_int⟩ :=
      exists_minimal_path_between G hX12_disj
        (Finset.disjoint_singleton_right.mpr (Finset.notMem_erase x _))
        (Finset.disjoint_singleton_right.mpr (Finset.notMem_erase x _))
        ⟨u0, hu0, w0, hw0, hreach⟩
    obtain ⟨hax, ha1⟩ := Finset.mem_erase.mp haX1
    obtain ⟨hbx, hb2⟩ := Finset.mem_erase.mp hbX2
    obtain ⟨arc1a, arc1b, harc1a, harc1b, h1a_pos, h1b_pos, h1_sum, h1a_sub, h1b_sub, _, _⟩ :=
      split_cycle G hc1 hx1 ha1 hax.symm
    obtain ⟨arc2a, arc2b, harc2a, harc2b, h2a_pos, h2b_pos, h2_sum, h2a_sub, h2b_sub, _, _⟩ :=
      split_cycle G hc2 hb2 hx2 hbx
    have hex_A1 : ∃ A1 : G.Walk x a, A1.IsPath ∧ 1 ≤ A1.length ∧ k ≤ 2 * A1.length ∧ walkVerts G A1 ⊆ walkVerts G c1 := by
      by_cases hle : arc1a.length ≤ arc1b.length
      · exact ⟨arc1b.reverse, harc1b.reverse, by simp; omega, by simp; omega, fun w hw => h1b_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw))⟩
      · exact ⟨arc1a, harc1a, h1a_pos, by omega, h1a_sub⟩
    have hex_A2 : ∃ A2 : G.Walk b x, A2.IsPath ∧ 1 ≤ A2.length ∧ k ≤ 2 * A2.length ∧ walkVerts G A2 ⊆ walkVerts G c2 := by
      by_cases hle : arc2a.length ≤ arc2b.length
      · exact ⟨arc2b.reverse, harc2b.reverse, by simp; omega, by simp; omega, fun w hw => h2b_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw))⟩
      · exact ⟨arc2a, harc2a, h2a_pos, by omega, h2a_sub⟩
    obtain ⟨A1, hA1_path, hA1_pos, hA1_len, hA1_sub⟩ := hex_A1
    obtain ⟨A2, hA2_path, hA2_pos, hA2_len, hA2_sub⟩ := hex_A2
    have hQ : (A1.append p).IsPath := isPath_append_of_inter_eq G A1 p hA1_path hp_path fun w hw1 hw2 => by
      by_contra hwa
      have hwc1 : w ∈ walkVerts G c1 := hA1_sub ((mem_walkVerts G).mpr hw1)
      have hwx : w ≠ x := fun h => hp_not_x w hw2 (by simp [h])
      have hwb : w ≠ b := fun h => Finset.disjoint_left.mp hX12_disj (Finset.mem_erase.mpr ⟨hwx, hwc1⟩) (h ▸ hbX2)
      exact (hp_int w hw2 hwa hwb).1 (Finset.mem_erase.mpr ⟨hwx, hwc1⟩)
    have hC_cyc : ((A1.append p).append A2).IsCycle := by
      refine cycle_of_two_paths G (A1.append p) A2 hQ hA2_path (Or.inl (by simp; omega)) fun w hw1 hw2 => ?_
      have hwc2 : w ∈ walkVerts G c2 := hA2_sub ((mem_walkVerts G).mpr hw2)
      rcases (Walk.mem_support_append_iff A1 p).mp hw1 with hwA1 | hwp
      · left
        have hm : w ∈ walkVerts G c1 ∩ walkVerts G c2 := Finset.mem_inter.mpr ⟨hA1_sub ((mem_walkVerts G).mpr hwA1), hwc2⟩
        rw [hx_eq, Finset.mem_singleton] at hm; exact hm
      · right; by_contra hwb
        have hwx : w ≠ x := fun h => hp_not_x w hwp (by simp [h])
        have hwa : w ≠ a := fun h => Finset.disjoint_left.mp hX12_disj (h ▸ haX1) (Finset.mem_erase.mpr ⟨hwx, hwc2⟩)
        exact (hp_int w hwp hwa hwb).2 (Finset.mem_erase.mpr ⟨hwx, hwc2⟩)
    have hle := hmax x _ hC_cyc
    simp only [Walk.length_append] at hle
    omega
  · -- Case 2: |c1 ∩ c2| = 2, say {x, y}
    obtain ⟨x, y, hxy, hxy_eq⟩ := Finset.card_eq_two.mp h2
    have hx_in : x ∈ walkVerts G c1 ∩ walkVerts G c2 := hxy_eq ▸ Finset.mem_insert_self x {y}
    have hy_in : y ∈ walkVerts G c1 ∩ walkVerts G c2 := hxy_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
    have hx1 : x ∈ walkVerts G c1 := (Finset.mem_inter.mp hx_in).1
    have hx2 : x ∈ walkVerts G c2 := (Finset.mem_inter.mp hx_in).2
    have hy1 : y ∈ walkVerts G c1 := (Finset.mem_inter.mp hy_in).1
    have hy2 : y ∈ walkVerts G c2 := (Finset.mem_inter.mp hy_in).2
    obtain ⟨A1, B1, hA1, hB1, hA1_pos, hB1_pos, h1_sum, hA1_sub, hB1_sub, h1_cov, h1_int⟩ :=
      split_cycle G hc1 hx1 hy1 hxy
    obtain ⟨A2, B2, hA2, hB2, hA2_pos, hB2_pos, h2_sum, hA2_sub, hB2_sub, h2_cov, h2_int⟩ :=
      split_cycle G hc2 hx2 hy2 hxy
    -- Combining any arc of c1 with any arc of c2 gives a cycle of length ≤ k!
    have harc_bound : ∀ (P1 : G.Walk x y) (P2 : G.Walk y x),
        P1.IsPath → P2.IsPath → 1 ≤ P1.length → 1 ≤ P2.length →
        walkVerts G P1 ⊆ walkVerts G c1 → walkVerts G P2 ⊆ walkVerts G c2 →
        P1.length + P2.length ≤ k := by
      intro P1 P2 hP1 hP2 hP1p hP2p hP1s hP2s
      by_cases h11 : P1.length = 1 ∧ P2.length = 1
      · omega
      · have hcyc : (P1.append P2).IsCycle := cycle_of_two_paths G P1 P2 hP1 hP2 (by omega) fun w hw1 hw2 => by
          have hm : w ∈ walkVerts G c1 ∩ walkVerts G c2 :=
            Finset.mem_inter.mpr ⟨hP1s ((mem_walkVerts G).mpr hw1), hP2s ((mem_walkVerts G).mpr hw2)⟩
          rw [hxy_eq, Finset.mem_insert, Finset.mem_singleton] at hm; exact hm
        have := hmax x _ hcyc
        simpa [Walk.length_append] using this
    have hb1 : A1.length + B2.length ≤ k := harc_bound A1 B2 hA1 hB2 hA1_pos hB2_pos hA1_sub hB2_sub
    have hb2 : B1.length + A2.length ≤ k := by
      have h2' := harc_bound B1.reverse A2.reverse hB1.reverse hA2.reverse (by simp; omega) (by simp; omega)
        (fun w hw => hB1_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw)))
        (fun w hw => hA2_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw)))
      simpa [Walk.length_reverse] using h2'
    have hb3 : A1.length + A2.length ≤ k := by
      have h3' := harc_bound A1 A2.reverse hA1 hA2.reverse hA1_pos (by simp; omega) hA1_sub
        (fun w hw => hA2_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw)))
      simpa [Walk.length_reverse] using h3'
    have hb4 : B1.length + B2.length ≤ k := by
      have h4' := harc_bound B1.reverse B2 hB1.reverse hB2 (by simp; omega) hB2_pos
        (fun w hw => hB1_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw))) hB2_sub
      simpa [Walk.length_reverse] using h4'
    -- Therefore A1.length = B1.length = A2.length = B2.length (and 2 * A1.length = k)!
    have heq_len : A1.length = B1.length ∧ A2.length = B2.length ∧ A1.length = A2.length := by omega
    -- Now G - {x, y} is connected! Find minimal path p in G - {x, y} from c1 \ {x, y} to c2 \ {x, y}.
    let X1 := walkVerts G c1 \ {x, y}
    let X2 := walkVerts G c2 \ {x, y}
    have hX1ne : X1.Nonempty := Finset.card_pos.mp (by
      have hsub : ({x, y} : Finset V) ⊆ walkVerts G c1 := fun z hz => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hxy, hcard1]; omega)
    have hX2ne : X2.Nonempty := Finset.card_pos.mp (by
      have hsub : ({x, y} : Finset V) ⊆ walkVerts G c2 := fun z hz => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hxy, hcard2]; omega)
    have hX12_disj : Disjoint X1 X2 := Finset.disjoint_left.mpr fun w hw1 hw2 => by
      have hm : w ∈ walkVerts G c1 ∩ walkVerts G c2 := Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hw1).1, (Finset.mem_sdiff.mp hw2).1⟩
      rw [hxy_eq] at hm; exact (Finset.mem_sdiff.mp hw1).2 hm
    obtain ⟨u0, hu0⟩ := hX1ne
    obtain ⟨w0, hw0⟩ := hX2ne
    have hreach : ReachAvoiding G {x, y} u0 w0 := by
      by_contra hnr
      exact h3conn {x, y} Finset.card_le_two ⟨u0, w0, (Finset.mem_sdiff.mp hu0).2, (Finset.mem_sdiff.mp hw0).2, hnr⟩
    obtain ⟨u, v, p, huX1, hvX2, hp_path, hp_pos, hp_not_xy, hp_int⟩ :=
      exists_minimal_path_between G hX12_disj Finset.sdiff_disjoint Finset.sdiff_disjoint
        ⟨u0, hu0, w0, hw0, hreach⟩
    obtain ⟨hu1, huxy⟩ := Finset.mem_sdiff.mp huX1
    obtain ⟨hv2, hvxy⟩ := Finset.mem_sdiff.mp hvX2
    have hux : u ≠ x := fun h => huxy (by simp [h])
    have huy : u ≠ y := fun h => huxy (by simp [h])
    have hvx : v ≠ x := fun h => hvxy (by simp [h])
    have hvy : v ≠ y := fun h => hvxy (by simp [h])
    -- Helper: given oriented arcs (P1 : x → y, Q1 : y → x) of c1 with u ∈ P1, and (P2 : x → y, Q2 : y → x) of c2 with v ∈ P2,
    -- form the two cycles P1[x..u] + p + P2[v..y] + Q1 and Q2 + P2[x..v] + p.reverse + P1[u..y]; sum of lengths = 2k + 2*p.length > 2k!
    have h2cyc_contra : ∀ (P1 : G.Walk x y) (Q1 : G.Walk y x) (P2 : G.Walk x y) (Q2 : G.Walk y x),
        P1.IsPath → Q1.IsPath → P2.IsPath → Q2.IsPath →
        P1.length + Q1.length = k → P2.length + Q2.length = k →
        walkVerts G P1 ⊆ walkVerts G c1 → walkVerts G Q1 ⊆ walkVerts G c1 →
        walkVerts G P2 ⊆ walkVerts G c2 → walkVerts G Q2 ⊆ walkVerts G c2 →
        (∀ w, w ∈ P1.support → w ∈ Q1.support → w = x ∨ w = y) →
        (∀ w, w ∈ P2.support → w ∈ Q2.support → w = x ∨ w = y) →
        u ∈ P1.support → v ∈ P2.support → False := by
      intro P1 Q1 P2 Q2 hP1 hQ1 hP2 hQ2 hlen1 hlen2 hP1s hQ1s hP2s hQ2s hP1Q1 hP2Q2 huP1 hvP2
      let P1x : G.Walk x u := P1.takeUntil u huP1
      let P1y : G.Walk u y := P1.dropUntil u huP1
      let P2x : G.Walk x v := P2.takeUntil v hvP2
      let P2y : G.Walk v y := P2.dropUntil v hvP2
      have hP1_eq : P1x.length + P1y.length = P1.length := by rw [← Walk.length_append, Walk.take_spec P1 huP1]
      have hP2_eq : P2x.length + P2y.length = P2.length := by rw [← Walk.length_append, Walk.take_spec P2 hvP2]
      have hP1x_path : P1x.IsPath := hP1.takeUntil huP1
      have hP1y_path : P1y.IsPath := hP1.dropUntil huP1
      have hP2x_path : P2x.IsPath := hP2.takeUntil hvP2
      have hP2y_path : P2y.IsPath := hP2.dropUntil hvP2
      have hP1x_sub : ∀ w ∈ P1x.support, w ∈ P1.support := fun w hw => Walk.support_takeUntil_subset P1 huP1 hw
      have hP1y_sub : ∀ w ∈ P1y.support, w ∈ P1.support := fun w hw => Walk.support_dropUntil_subset P1 huP1 hw
      have hP2x_sub : ∀ w ∈ P2x.support, w ∈ P2.support := fun w hw => Walk.support_takeUntil_subset P2 hvP2 hw
      have hP2y_sub : ∀ w ∈ P2y.support, w ∈ P2.support := fun w hw => Walk.support_dropUntil_subset P2 hvP2 hw
      have hP1x_no_y : y ∉ P1x.support := fun hy => by
        have hspec := Walk.take_spec P1 huP1
        have hnd := hP1.support_nodup
        rw [← hspec, Walk.support_append, List.nodup_append'] at hnd
        have hy_tail : y ∈ P1y.support.tail := by
          have hy_in : y ∈ P1y.support := Walk.end_mem_support P1y
          rw [← P1y.cons_tail_support, List.mem_cons] at hy_in
          exact hy_in.resolve_left huy.symm
        exact List.disjoint_left.mp hnd.2.2 hy hy_tail
      have hP2y_no_x : x ∉ P2y.support := fun hx => by
        have hspec := Walk.take_spec P2 hvP2
        have hnd := hP2.support_nodup
        rw [← hspec, Walk.support_append, List.nodup_append'] at hnd
        have hx_in : x ∈ P2x.support := Walk.start_mem_support P2x
        have hx_tail : x ∈ P2y.support.tail := by
          rw [← P2y.cons_tail_support, List.mem_cons] at hx
          exact hx.resolve_left hvx.symm
        exact List.disjoint_left.mp hnd.2.2 hx_in hx_tail
      have hP2x_no_y : y ∉ P2x.support := fun hy => by
        have hspec := Walk.take_spec P2 hvP2
        have hnd := hP2.support_nodup
        rw [← hspec, Walk.support_append, List.nodup_append'] at hnd
        have hy_tail : y ∈ P2y.support.tail := by
          have hy_in : y ∈ P2y.support := Walk.end_mem_support P2y
          rw [← P2y.cons_tail_support, List.mem_cons] at hy_in
          exact hy_in.resolve_left hvy.symm
        exact List.disjoint_left.mp hnd.2.2 hy hy_tail
      have hP1y_no_x : x ∉ P1y.support := fun hx => by
        have hspec := Walk.take_spec P1 huP1
        have hnd := hP1.support_nodup
        rw [← hspec, Walk.support_append, List.nodup_append'] at hnd
        have hx_in : x ∈ P1x.support := Walk.start_mem_support P1x
        have hx_tail : x ∈ P1y.support.tail := by
          rw [← P1y.cons_tail_support, List.mem_cons] at hx
          exact hx.resolve_left hux.symm
        exact List.disjoint_left.mp hnd.2.2 hx_in hx_tail
      -- Cycle 1: C' = ((P1x.append p).append P2y).append Q1 : x → x
      have hpath1a : (P1x.append p).IsPath := isPath_append_of_inter_eq G P1x p hP1x_path hp_path fun w hw1 hw2 => by
        by_contra hwu
        have hwc1 : w ∈ walkVerts G c1 := hP1s ((mem_walkVerts G).mpr (hP1x_sub w hw1))
        have hwxy : w ∉ ({x, y} : Finset V) := hp_not_xy w hw2
        have hwv : w ≠ v := fun h => Finset.disjoint_left.mp hX12_disj (Finset.mem_sdiff.mpr ⟨hwc1, hwxy⟩) (h ▸ hvX2)
        exact (hp_int w hw2 hwu hwv).1 (Finset.mem_sdiff.mpr ⟨hwc1, hwxy⟩)
      have hpath1b : ((P1x.append p).append P2y).IsPath :=
        isPath_append_of_inter_eq G (P1x.append p) P2y hpath1a hP2y_path fun w hw1 hw2 => by
          have hwc2 : w ∈ walkVerts G c2 := hP2s ((mem_walkVerts G).mpr (hP2y_sub w hw2))
          rcases (Walk.mem_support_append_iff P1x p).mp hw1 with hwP1x | hwp
          · exfalso
            have hm : w ∈ walkVerts G c1 ∩ walkVerts G c2 :=
              Finset.mem_inter.mpr ⟨hP1s ((mem_walkVerts G).mpr (hP1x_sub w hwP1x)), hwc2⟩
            rw [hxy_eq, Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with rfl | rfl
            · exact hP2y_no_x hw2
            · exact hP1x_no_y hwP1x
          · by_contra hwv
            have hwxy : w ∉ ({x, y} : Finset V) := hp_not_xy w hwp
            have hwu : w ≠ u := fun h => Finset.disjoint_left.mp hX12_disj (h ▸ huX1) (Finset.mem_sdiff.mpr ⟨hwc2, hwxy⟩)
            exact (hp_int w hwp hwu hwv).2 (Finset.mem_sdiff.mpr ⟨hwc2, hwxy⟩)
      have hC1 : (((P1x.append p).append P2y).append Q1).IsCycle := by
        have hP1x_pos : 1 ≤ P1x.length := by cases P1x with | nil => exact absurd rfl hux.symm | cons _ _ => simp
        refine cycle_of_two_paths G ((P1x.append p).append P2y) Q1 hpath1b hQ1
          (Or.inl (by simp; omega))
          fun w hw1 hw2 => ?_
        have hwc1Q : w ∈ walkVerts G c1 := hQ1s ((mem_walkVerts G).mpr hw2)
        rcases (Walk.mem_support_append_iff (P1x.append p) P2y).mp hw1 with hw1a | hwP2y
        · rcases (Walk.mem_support_append_iff P1x p).mp hw1a with hwP1x | hwp
          · exact hP1Q1 w (hP1x_sub w hwP1x) hw2
          · exfalso
            have hwxy : w ∉ ({x, y} : Finset V) := hp_not_xy w hwp
            have hwu : w ≠ u := fun h => by rcases hP1Q1 u huP1 (h ▸ hw2) with h1 | h2; exact hux h1; exact huy h2
            have hwv : w ≠ v := fun h => Finset.disjoint_left.mp hX12_disj (Finset.mem_sdiff.mpr ⟨hwc1Q, hwxy⟩) (h ▸ hvX2)
            exact (hp_int w hwp hwu hwv).1 (Finset.mem_sdiff.mpr ⟨hwc1Q, hwxy⟩)
        · have hm : w ∈ walkVerts G c1 ∩ walkVerts G c2 :=
            Finset.mem_inter.mpr ⟨hwc1Q, hP2s ((mem_walkVerts G).mpr (hP2y_sub w hwP2y))⟩
          rw [hxy_eq, Finset.mem_insert, Finset.mem_singleton] at hm; exact hm
      -- Cycle 2: C'' = ((P2x.append p.reverse).append P1y).append Q2 : x → x
      have hpath2a : (P2x.append p.reverse).IsPath := isPath_append_of_inter_eq G P2x p.reverse hP2x_path hp_path.reverse fun w hw1 hw2 => by
        by_contra hwv
        have hwc2 : w ∈ walkVerts G c2 := hP2s ((mem_walkVerts G).mpr (hP2x_sub w hw1))
        have hw2' : w ∈ p.support := by simpa using hw2
        have hwxy : w ∉ ({x, y} : Finset V) := hp_not_xy w hw2'
        have hwu : w ≠ u := fun h => Finset.disjoint_left.mp hX12_disj (h ▸ huX1) (Finset.mem_sdiff.mpr ⟨hwc2, hwxy⟩)
        exact (hp_int w hw2' hwu hwv).2 (Finset.mem_sdiff.mpr ⟨hwc2, hwxy⟩)
      have hpath2b : ((P2x.append p.reverse).append P1y).IsPath :=
        isPath_append_of_inter_eq G (P2x.append p.reverse) P1y hpath2a hP1y_path fun w hw1 hw2 => by
          have hwc1 : w ∈ walkVerts G c1 := hP1s ((mem_walkVerts G).mpr (hP1y_sub w hw2))
          rcases (Walk.mem_support_append_iff P2x p.reverse).mp hw1 with hwP2x | hwp
          · exfalso
            have hm : w ∈ walkVerts G c1 ∩ walkVerts G c2 :=
              Finset.mem_inter.mpr ⟨hwc1, hP2s ((mem_walkVerts G).mpr (hP2x_sub w hwP2x))⟩
            rw [hxy_eq, Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with rfl | rfl
            · exact hP1y_no_x hw2
            · exact hP2x_no_y hwP2x
          · by_contra hwu
            have hwp' : w ∈ p.support := by simpa using hwp
            have hwxy : w ∉ ({x, y} : Finset V) := hp_not_xy w hwp'
            have hwv : w ≠ v := fun h => Finset.disjoint_left.mp hX12_disj (Finset.mem_sdiff.mpr ⟨hwc1, hwxy⟩) (h ▸ hvX2)
            exact (hp_int w hwp' hwu hwv).1 (Finset.mem_sdiff.mpr ⟨hwc1, hwxy⟩)
      have hC2 : (((P2x.append p.reverse).append P1y).append Q2).IsCycle := by
        have hP2x_pos : 1 ≤ P2x.length := by cases P2x with | nil => exact absurd rfl hvx.symm | cons _ _ => simp
        refine cycle_of_two_paths G ((P2x.append p.reverse).append P1y) Q2 hpath2b hQ2
          (Or.inl (by simp; omega))
          fun w hw1 hw2 => ?_
        have hwc2Q : w ∈ walkVerts G c2 := hQ2s ((mem_walkVerts G).mpr hw2)
        rcases (Walk.mem_support_append_iff (P2x.append p.reverse) P1y).mp hw1 with hw2a | hwP1y
        · rcases (Walk.mem_support_append_iff P2x p.reverse).mp hw2a with hwP2x | hwp
          · exact hP2Q2 w (hP2x_sub w hwP2x) hw2
          · exfalso
            have hwp' : w ∈ p.support := by simpa using hwp
            have hwxy : w ∉ ({x, y} : Finset V) := hp_not_xy w hwp'
            have hwv : w ≠ v := fun h => by rcases hP2Q2 v hvP2 (h ▸ hw2) with h1 | h2; exact hvx h1; exact hvy h2
            have hwu : w ≠ u := fun h => Finset.disjoint_left.mp hX12_disj (h ▸ huX1) (Finset.mem_sdiff.mpr ⟨hwc2Q, hwxy⟩)
            exact (hp_int w hwp' hwu hwv).2 (Finset.mem_sdiff.mpr ⟨hwc2Q, hwxy⟩)
        · have hm : w ∈ walkVerts G c1 ∩ walkVerts G c2 :=
            Finset.mem_inter.mpr ⟨hP1s ((mem_walkVerts G).mpr (hP1y_sub w hwP1y)), hwc2Q⟩
          rw [hxy_eq, Finset.mem_insert, Finset.mem_singleton] at hm; exact hm
      have hle1 := hmax x _ hC1
      have hle2 := hmax x _ hC2
      simp only [Walk.length_append, Walk.length_reverse] at hle1 hle2
      omega
    -- Split on which arc of c1 contains u, and which arc of c2 contains v!
    rcases h1_cov u hu1 with huA1 | huB1 <;> rcases h2_cov v hv2 with hvA2 | hvB2
    · exact h2cyc_contra A1 B1 A2 B2 hA1 hB1 hA2 hB2 (h1_sum.trans hl1) (h2_sum.trans hl2)
        hA1_sub hB1_sub hA2_sub hB2_sub h1_int h2_int huA1 hvA2
    · exact h2cyc_contra A1 B1 B2.reverse A2.reverse hA1 hB1 hB2.reverse hA2.reverse
        (h1_sum.trans hl1) (by simp; omega) hA1_sub hB1_sub
        (fun w hw => hB2_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw)))
        (fun w hw => hA2_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw)))
        h1_int (fun w h1 h2 => h2_int w (by simpa using h2) (by simpa using h1))
        huA1 (by simpa using hvB2)
    · exact h2cyc_contra B1.reverse A1.reverse A2 B2 hB1.reverse hA1.reverse hA2 hB2
        (by simp; omega) (h2_sum.trans hl2)
        (fun w hw => hB1_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw)))
        (fun w hw => hA1_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw)))
        hA2_sub hB2_sub
        (fun w h1 h2 => h1_int w (by simpa using h2) (by simpa using h1)) h2_int
        (by simpa using huB1) hvA2
    · exact h2cyc_contra B1.reverse A1.reverse B2.reverse A2.reverse hB1.reverse hA1.reverse hB2.reverse hA2.reverse
        (by simp; omega) (by simp; omega)
        (fun w hw => hB1_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw)))
        (fun w hw => hA1_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw)))
        (fun w hw => hB2_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw)))
        (fun w hw => hA2_sub ((mem_walkVerts G).mpr (by simpa using (mem_walkVerts G).mp hw)))
        (fun w h1 h2 => h1_int w (by simpa using h2) (by simpa using h1))
        (fun w h1 h2 => h2_int w (by simpa using h2) (by simpa using h1))
        (by simpa using huB1) (by simpa using hvB2)

end CycleIntersection

section DoubleCounting

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Double counting over Aut(G): if every translate of S meets S in at least c vertices, then
c * |V| ≤ |S|^2. -/
lemma double_count_aut (htrans : IsVertexTransitive G) (S : Finset V) (c : ℕ)
    (hinter : ∀ φ : G ≃g G, c ≤ (S ∩ S.image φ).card) :
    c * Fintype.card V ≤ S.card ^ 2 := by
  classical
  -- Fintype instance on G ≃g G via injection into Equiv.Perm V
  let toPerm : (G ≃g G) → Equiv.Perm V := fun φ => φ.toEquiv
  have htoPerm_inj : Function.Injective toPerm := fun φ ψ h => by
    ext x; exact congrArg (fun e : Equiv.Perm V => e x) h
  letI : Fintype (G ≃g G) := Fintype.ofInjective toPerm htoPerm_inj
  have hAut_pos : 0 < Fintype.card (G ≃g G) := Fintype.card_pos_iff.mpr ⟨RelIso.refl G.Adj⟩
  -- For any u, v : V, the fiber {φ | φ u = v} has size |Aut(G)| / |V|, i.e., |V| * |fiber u v| = |Aut(G)|
  have hfiber_eq : ∀ u v1 v2 : V,
      (Finset.univ.filter (fun φ : G ≃g G => φ u = v1)).card =
      (Finset.univ.filter (fun φ : G ≃g G => φ u = v2)).card := by
    intro u v1 v2
    obtain ⟨ψ, hψ⟩ := htrans v1 v2
    apply Finset.card_bij (fun φ _ => φ.trans ψ)
    · intro φ hφ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ ⊢
      change ψ (φ u) = v2; rw [hφ, hψ]
    · intro φ1 _ φ2 _ heq
      ext x; exact ψ.injective (congrArg (fun f : G ≃g G => f x) heq)
    · intro φ hφ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ
      refine ⟨φ.trans ψ.symm, ?_, by ext x; simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change ψ.symm (φ u) = v1; rw [hφ, ← hψ, ψ.symm_apply_apply]
  have hfiber_mul : ∀ u v : V,
      Fintype.card V * (Finset.univ.filter (fun φ : G ≃g G => φ u = v)).card = Fintype.card (G ≃g G) := by
    intro u v
    have hsum := Finset.card_eq_sum_card_fiberwise (f := fun φ : G ≃g G => φ u)
      (s := (Finset.univ : Finset (G ≃g G))) (t := (Finset.univ : Finset V)) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ] at hsum
    have hconst : ∑ w : V, (Finset.univ.filter (fun φ : G ≃g G => φ u = w)).card =
        Fintype.card V * (Finset.univ.filter (fun φ : G ≃g G => φ u = v)).card := by
      rw [Finset.sum_congr rfl (fun w _ => hfiber_eq u w v), Finset.sum_const, Finset.card_univ, smul_eq_mul]
    omega
  -- Sum |S ∩ S.image φ| over all φ : G ≃g G
  have hlow : c * Fintype.card (G ≃g G) ≤ ∑ φ : G ≃g G, (S ∩ S.image φ).card := by
    calc c * Fintype.card (G ≃g G)
        = ∑ _φ : G ≃g G, c := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
      _ ≤ ∑ φ : G ≃g G, (S ∩ S.image φ).card := Finset.sum_le_sum (fun φ _ => hinter φ)
  have hdouble : ∑ φ : G ≃g G, (S ∩ S.image φ).card =
      ∑ u ∈ S, ∑ v ∈ S, (Finset.univ.filter (fun φ : G ≃g G => φ u = v)).card := by
    have h1 : ∀ φ : G ≃g G, (S ∩ S.image φ).card =
        ∑ u ∈ S, ∑ v ∈ S, if φ u = v then 1 else 0 := by
      intro φ
      have heq : (S ∩ S.image φ).card = (S.filter (fun u => φ u ∈ S)).card := by
        apply Finset.card_bij (fun y _ => φ.symm y)
        · intro y hy
          obtain ⟨hyS, hyImg⟩ := Finset.mem_inter.mp hy
          obtain ⟨u, huS, rfl⟩ := Finset.mem_image.mp hyImg
          rw [Finset.mem_filter, φ.symm_apply_apply]
          exact ⟨huS, hyS⟩
        · intro a _ b _ hab; exact φ.symm.injective hab
        · intro u hu
          obtain ⟨huS, hφuS⟩ := Finset.mem_filter.mp hu
          exact ⟨φ u, Finset.mem_inter.mpr ⟨hφuS, Finset.mem_image.mpr ⟨u, huS, rfl⟩⟩, φ.symm_apply_apply u⟩
      rw [heq, Finset.card_filter]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases h : φ u ∈ S
      · simp [h, Finset.sum_ite_eq']
      · simp [h, Finset.sum_ite_eq']
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.card_filter]
  -- Multiply by |V| and cancel |Aut(G)| > 0!
  have hmul : Fintype.card V * (c * Fintype.card (G ≃g G)) ≤
      Fintype.card V * (∑ u ∈ S, ∑ v ∈ S, (Finset.univ.filter (fun φ : G ≃g G => φ u = v)).card) := by
    rw [← hdouble]; exact Nat.mul_le_mul_left _ hlow
  have hrhs : Fintype.card V * (∑ u ∈ S, ∑ v ∈ S, (Finset.univ.filter (fun φ : G ≃g G => φ u = v)).card) =
      S.card ^ 2 * Fintype.card (G ≃g G) := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum, hfiber_mul, Finset.sum_const, smul_eq_mul]
    ring
  rw [hrhs] at hmul
  have hle : c * Fintype.card V * Fintype.card (G ≃g G) ≤ S.card ^ 2 * Fintype.card (G ≃g G) := by
    linarith
  exact Nat.le_of_mul_le_mul_right hle hAut_pos

end DoubleCounting

end OMA.LovaszBabai

open SimpleGraph LovaszConjecture OMA.LovaszBabai in
theorem OMA.solution : type_of% @LovaszConjecture.lovasz_conjecture.variants.babai := by
  intro V _ _ G _ hconn htrans hcard
  classical
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hdeg2 : ∀ v : V, 2 ≤ G.degree v := two_le_degree_of_connected_trans G hconn htrans hcard
  let v0 : V := Classical.arbitrary V
  by_cases hd2 : G.degree v0 = 2
  · -- Case d = 2: single cycle of length n ≥ 3
    have hall2 : ∀ v : V, G.degree v = 2 := fun v => by
      rw [degree_eq_of_isVertexTransitive G htrans v v0, hd2]
    obtain ⟨v, c, hc, hlen⟩ := case_deg_two G hconn hall2 hcard
    refine ⟨v, c, hc, ?_⟩
    rw [hlen]
    have hsq : (3 * Fintype.card V : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
      have hn : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hcard
      nlinarith
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩
  · -- Case d ≥ 3: 3-connected by Watkins' theorem, longest cycles intersect in ≥ 3 vertices!
    have hdeg3 : ∀ v : V, 3 ≤ G.degree v := fun v => by
      have h1 := hdeg2 v0
      have h2 := degree_eq_of_isVertexTransitive G htrans v v0
      omega
    have h3conn : ∀ S : Finset V, S.card ≤ 2 → ¬ IsSeparating G S :=
      no_separating_le_two G hconn htrans hdeg3
    -- Pick a longest cycle c of length k
    obtain ⟨vc0, c0, hc0⟩ := exists_cycle_of_two_le_degree G hdeg2
    let L : Finset ℕ := (Finset.range (Fintype.card V + 1)).filter
      (fun l => ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = l)
    have hLne : L.Nonempty := ⟨c0.length, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (cycle_length_le_card G hc0)), vc0, c0, hc0, rfl⟩⟩
    let k := L.max' hLne
    have hk_mem := Finset.max'_mem L hLne
    obtain ⟨v, c, hc, hclen⟩ := (Finset.mem_filter.mp hk_mem).2
    have hmax : ∀ (w : V) (c' : G.Walk w w), c'.IsCycle → c'.length ≤ k := fun w c' hc' =>
      Finset.le_max' L c'.length (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (cycle_length_le_card G hc')), w, c', hc', rfl⟩)
    -- Every translate φ(c) intersects c in at least 3 vertices!
    have hinter : ∀ φ : G ≃g G, 3 ≤ (walkVerts G c ∩ (walkVerts G c).image φ).card := by
      intro φ
      have himg : walkVerts G (mapWalk G φ c) = (walkVerts G c).image φ := by
        ext y
        simp only [mem_walkVerts, mapWalk_support, List.mem_map, Finset.mem_image]
      rw [← himg]
      exact three_le_card_inter_longest_cycles G hconn h3conn hmax hc (mapWalk_isCycle G φ hc)
        hclen ((mapWalk_length G φ c).trans hclen)
    have h3n : 3 * Fintype.card V ≤ (walkVerts G c).card ^ 2 :=
      double_count_aut G htrans (walkVerts G c) 3 hinter
    rw [card_walkVerts_of_isCycle G hc, hclen] at h3n
    refine ⟨v, c, hc, ?_⟩
    rw [hclen]
    have hsq : (3 * Fintype.card V : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast h3n
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩
