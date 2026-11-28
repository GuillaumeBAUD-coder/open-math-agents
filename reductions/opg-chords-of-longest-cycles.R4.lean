import OMAStatements.S_opg_chords_of_longest_cycles
import Mathlib.Tactic

/-!
# Reduction R4 of the chord conjecture (opg-chords-of-longest-cycles)

Target: EVERY longest cycle of a finite 3-connected simple graph has a chord (Open Problem Garden,
C. Thomassen). The strong form is OPEN (Thomassen, JCTB 179 (2026) 90-117, proves only that SOME
longest cycle has a chord; the strong form is known for 2-connected cubic graphs, planar graphs of
minimum degree 4, the projective plane, the torus and the Klein bottle at connectivity 4, and
graphs of minimum degree at least 5.0368 sqrt n + 1 by Harvey, EJC 2017).

R2 split the target into the two open non-Hamiltonian cases (off-cycle vertices connected versus
disconnected) after proving the Hamiltonian case in-file. R4 goes one step further and also
discharges the case of exactly ONE vertex off the cycle, so the two hypotheses now only concern
non-spanning longest cycles with AT LEAST TWO vertices off them. The proof of the one-vertex case
is the observation that a counterexample has to be tight in degree:

* `hasChord_of_spanning_isCycle` (proved here): a spanning cycle in a graph of minimum degree at
  least 3 has a chord, because without one every graph edge is a cycle edge, so the degree sum is
  twice the cycle length while minimum degree forces it to be three times the vertex count.
* `one_off_no_chordless_longest` (proved here): if a chordless longest cycle `c` has exactly one
  vertex `x` off it, then every vertex of `c` is adjacent to `x` - otherwise chordlessness and the
  fact that all its neighbours lie on `c` give that vertex degree at most 2. Then
  `x, c 0, c 1, ..., c (length - 1), x` is a cycle of length `length + 1`, contradicting
  maximality. Equivalently `hasChord_of_one_off` and `hasChord_of_card_succ`: a longest cycle with
  card V = length + 1 has a chord.
* `min_degree_three` and `card_ge_four`: 3-connected graphs have minimum degree at least 3 and at
  least four vertices (the 3-connectivity hypothesis is only used through these two facts here).

So `main` is a four-way exhaustive case split: spanning (proved), one vertex off (proved), at least
two vertices off with connected off-cycle set (`H1`), at least two vertices off with disconnected
off-cycle set (`H2`). Both remaining hypotheses are open. They are inhabited: K_{3,4} and K_{3,5}
are 3-connected with minimum degree 4 and have a chordless longest cycle.
-/

namespace OMA.R_opg_chords_of_longest_cycles_R4

open OMA.S_opg_chords_of_longest_cycles

/-- The chord conjecture for a non-spanning longest cycle whose off-cycle vertex set is connected
and has at least two vertices. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsKConnected G 3 →
    ∀ (u : V) (c : G.Walk u u), IsLongestCycle c →
      (∃ v : V, v ∉ c.support) →
      (∃ v w : V, v ≠ w ∧ v ∉ c.support ∧ w ∉ c.support) →
      (G.induce {v : V | v ∉ c.support}).Connected → HasChord c

/-- The chord conjecture for a non-spanning longest cycle whose off-cycle vertex set is
disconnected (it then automatically has at least two vertices). -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsKConnected G 3 →
    ∀ (u : V) (c : G.Walk u u), IsLongestCycle c → (∃ v : V, v ∉ c.support) →
      ¬ (G.induce {v : V | v ∉ c.support}).Connected → HasChord c

variable {V : Type} [Fintype V]

/-- (T1) A 3-connected graph has at least 4 vertices. -/
theorem card_ge_four_of_isKConnected (G : SimpleGraph V) (h : IsKConnected G 3) :
    4 ≤ Fintype.card V := by
  have h3 : 3 < Fintype.card V := h.1
  omega

section T2

omit [Fintype V] in
/-- In the graph induced on the complement of `S`, a vertex `v ∉ S` whose neighbours all lie in
`S` has no neighbours at all. -/
theorem neighborSet_induce_compl_eq_empty (G : SimpleGraph V) (S : Finset V) (v : V) (hv : v ∉ S)
    (hall : ∀ w, G.Adj v w → w ∈ S) :
    (G.induce ((((↑S : Set V))ᶜ))).neighborSet ⟨v, by simpa using hv⟩ = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ⟨w, hw⟩ hadj
  have h1 : G.Adj v w := SimpleGraph.induce_adj.mp hadj
  exact hw (by simpa using hall w h1)

/-- If `v`'s neighbourhood `S` is small and deleting `S` keeps the graph connected then the graph
has at most card S + 1 vertices. -/
theorem card_le_succ_of_connected_induce_compl (G : SimpleGraph V) (v : V) (S : Finset V)
    (hvS : v ∉ S) (hall : ∀ w, G.Adj v w → w ∈ S)
    (hconn : (G.induce ((((↑S : Set V))ᶜ))).Connected) :
    Fintype.card V ≤ S.card + 1 := by
  classical
  have hempty : (G.induce ((((↑S : Set V))ᶜ))).neighborSet ⟨v, by simpa using hvS⟩ = ∅ :=
    neighborSet_induce_compl_eq_empty G S v hvS hall
  have hsingle : ∀ x : ↥(((↑S : Set V))ᶜ), x = ⟨v, by simpa using hvS⟩ := by
    intro x
    by_contra hne
    exact SimpleGraph.not_reachable_of_neighborSet_left_eq_empty (fun h => hne h.symm) hempty
      (hconn.preconnected ⟨v, by simpa using hvS⟩ x)
  have hsub : Sᶜ ⊆ {v} := by
    intro x hx
    have hx' : (⟨x, by simpa using hx⟩ : ↥(((↑S : Set V))ᶜ))
        = ⟨v, by simpa using hvS⟩ := hsingle ⟨x, by simpa using hx⟩
    have := congrArg Subtype.val hx'
    simpa using this
  have hcompl : Sᶜ = {v} := by
    refine Finset.Subset.antisymm hsub ?_
    rw [Finset.singleton_subset_iff]
    simp [hvS]
  have hcard : Fintype.card V = S.card + Sᶜ.card := (Finset.card_add_card_compl S).symm
  rw [hcompl, Finset.card_singleton] at hcard
  omega

/-- (T2) A 3-connected graph has minimum degree at least 3. -/
theorem min_degree_three (G : SimpleGraph V) [DecidableRel G.Adj] (h : IsKConnected G 3) (v : V) :
    3 ≤ G.degree v := by
  by_contra hdeg
  have hfour : 4 ≤ Fintype.card V := card_ge_four_of_isKConnected G h
  have hScard : (G.neighborFinset v).card ≤ 2 := by
    have hd : (G.neighborFinset v).card = G.degree v := rfl
    omega
  have hvS : v ∉ (G.neighborFinset v) := G.notMem_neighborFinset_self v
  have hall : ∀ w, G.Adj v w → w ∈ G.neighborFinset v := by
    intro w hw
    simpa using hw
  have hconn : (G.induce ((((↑(G.neighborFinset v) : Set V))ᶜ))).Connected := by
    have := h.2 (G.neighborFinset v) (by omega)
    simpa using this
  have hle := card_le_succ_of_connected_induce_compl G v (G.neighborFinset v) hvS hall hconn
  omega

end T2
section T3

open SimpleGraph

omit [Fintype V] in
/-- A chordless walk whose two endpoints are in its support: an edge of the graph with both ends on
the walk is an edge of the walk. -/
theorem mem_edges_of_isChordless {G : SimpleGraph V} {u : V} {c : G.Walk u u}
    (hcl : c.IsChordless) (hspan : ∀ v : V, v ∈ c.support) {x y : V} (hxy : G.Adj x y) :
    s(x, y) ∈ c.edges :=
  hcl.mem_edges (hspan x) (hspan y) hxy

/-- Core counting lemma: a cycle all of whose edges at the basepoint `u` are cycle edges forces
`G.degree u ≤ 2`, so a vertex of degree at least 3 forces a chord. -/
theorem hasChord_of_adj_mem_edges (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    (c : G.Walk u u) (hc : c.IsCycle) (hedge : ∀ w : V, G.Adj u w → s(u, w) ∈ c.edges)
    (hdeg : 3 ≤ G.degree u) : HasChord c := by
  classical
  by_contra hno
  -- the only neighbours of the basepoint are the second and the penultimate vertex
  have hnb : ∀ w : V, G.Adj u w → w = c.snd ∨ w = c.penultimate := by
    intro w hw
    have hmem : s(u, w) ∈ c.edges := hedge w hw
    obtain ⟨i, hi, hsi⟩ := (SimpleGraph.Walk.mk_mem_edges_iff_exists c).mp hmem
    rw [Sym2.eq_iff] at hsi
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hsi
    · left
      rcases hc.getVert_endpoint_iff (le_of_lt hi) |>.mp h1 with h0 | htop
      · rw [← h2, h0]
      · omega
    · right
      have htop : i + 1 = c.length := by
        rcases hc.getVert_endpoint_iff (by omega : i + 1 ≤ c.length) |>.mp h2 with h0 | htop
        · omega
        · exact htop
      have hlast : i = c.length - 1 := by omega
      rw [← h1, hlast]
  have hsub : G.neighborFinset u ⊆ ({c.snd, c.penultimate} : Finset V) := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    rcases hnb w hw with rfl | rfl <;> simp
  have hpair : ({c.snd, c.penultimate} : Finset V).card ≤ 2 := by
    have h := Finset.card_insert_le c.snd ({c.penultimate} : Finset V)
    simp only [Finset.card_singleton] at h
    omega
  have hle : G.degree u ≤ 2 := by
    have h1 : G.degree u = (G.neighborFinset u).card := rfl
    rw [h1]
    exact le_trans (Finset.card_le_card hsub) hpair
  omega

/-- (T3) A spanning cycle in a graph of minimum degree at least 3 has a chord. -/
theorem hasChord_of_spanning_isCycle (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    (c : G.Walk u u) (hc : c.IsCycle) (hspan : ∀ v : V, v ∈ c.support)
    (hdeg : ∀ v : V, 3 ≤ G.degree v) : HasChord c := by
  classical
  by_contra hno
  have hcl : c.IsChordless := fun e => by
    induction e using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.Walk.isChord_sym2Mk]
      rintro ⟨hadj, hnotmem, hx, hy⟩
      exact hno ⟨x, y, hadj, hx, hy, hnotmem⟩
  exact hno (hasChord_of_adj_mem_edges G u c hc
    (fun w hw => mem_edges_of_isChordless hcl hspan hw) (hdeg u))

omit [Fintype V] in
/-- `HasChord` is invariant under rotating a cycle to a different basepoint. -/
theorem hasChord_rotate_iff (G : SimpleGraph V) [DecidableEq V] {u : V} (c : G.Walk u u) (v : V)
    (hv : v ∈ c.support) : HasChord (c.rotate v hv) ↔ HasChord c := by
  have hmem : ∀ w : V, w ∈ (c.rotate v hv).support ↔ w ∈ c.support :=
    fun w => by rw [SimpleGraph.Walk.mem_support_rotate_iff]
  have hedge : ∀ e : Sym2 V, e ∈ (c.rotate v hv).edges ↔ e ∈ c.edges :=
    fun e => (SimpleGraph.Walk.rotate_edges c v hv).perm.mem_iff
  constructor
  · rintro ⟨x, y, hadj, hx, hy, hne⟩
    exact ⟨x, y, hadj, (hmem x).mp hx, (hmem y).mp hy, fun h => hne ((hedge s(x, y)).mpr h)⟩
  · rintro ⟨x, y, hadj, hx, hy, hne⟩
    exact ⟨x, y, hadj, (hmem x).mpr hx, (hmem y).mpr hy, fun h => hne ((hedge s(x, y)).mp h)⟩

/-- (T3, local/fallback form) If `v` lies on the cycle `c`, all neighbours of `v` lie on `c`, and
`degree v ≥ 3`, then `c` has a chord.  No spanning hypothesis is needed. -/
theorem hasChord_of_neighbors_mem_support (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V]
    (u : V)
    (c : G.Walk u u) (hc : c.IsCycle) (v : V) (hv : v ∈ c.support)
    (hloc : ∀ w : V, G.Adj v w → w ∈ c.support) (hdeg : 3 ≤ G.degree v) : HasChord c := by
  classical
  by_contra hno
  -- every edge of `c` with ends on `c` is an edge of `c`
  have hcl : c.IsChordless := fun e => by
    induction e using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.Walk.isChord_sym2Mk]
      rintro ⟨hadj, hnotmem, hx, hy⟩
      exact hno ⟨x, y, hadj, hx, hy, hnotmem⟩
  -- move the basepoint to `v`
  have hrc : (c.rotate v hv).IsCycle := hc.rotate hv
  have hedge : ∀ w : V, G.Adj v w → s(v, w) ∈ (c.rotate v hv).edges := by
    intro w hw
    have hin : s(v, w) ∈ c.edges := hcl.mem_edges hv (hloc w hw) hw
    exact (SimpleGraph.Walk.rotate_edges c v hv).perm.mem_iff.mpr hin
  exact hno ((hasChord_rotate_iff G c v hv).mp
    (hasChord_of_adj_mem_edges G v (c.rotate v hv) hrc hedge hdeg))

end T3
section OneOff

/-- A chordless cycle is not a longest cycle of a 3-connected graph if exactly one vertex `x` lies
off it.  (Equivalently: `x` must be adjacent to every vertex of the cycle, whence splicing `x`
into the cycle gives a strictly longer cycle.) -/
theorem one_off_no_chordless_longest (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsKConnected G 3) {u : V} {c : G.Walk u u} (hlc : IsLongestCycle c)
    (hch : c.IsChordless) {x : V} (hx : x ∉ c.support)
    (honly : ∀ y : V, y ∉ c.support → y = x) : False := by
  classical
  have hc : c.IsCycle := hlc.1
  -- `HasChord` is exactly the negation of chordlessness
  have hnoChord : ¬ HasChord c := by
    rintro ⟨a, b, hab, ha, hb, hne⟩
    exact hch (SimpleGraph.Walk.isChord_sym2Mk.mpr ⟨hab, hne, ha, hb⟩)
  -- step 1: every vertex of the cycle is adjacent to `x`
  have hadj : ∀ v : V, v ∈ c.support → G.Adj x v := by
    intro v hv
    by_contra hnv
    refine hnoChord (hasChord_of_neighbors_mem_support G u c hc v hv ?_
      (min_degree_three G hG v))
    intro w hw
    by_contra hwmem
    rw [honly w hwmem] at hw
    exact hnv hw.symm
  have hcnil : ¬ c.Nil := hc.not_nil
  -- `x` is adjacent to the start and to the penultimate vertex, and `x ∉ c.dropLast.support`
  have hxu : G.Adj x u := hadj u c.start_mem_support
  have hpen_supp : c.penultimate ∈ c.support := by
    have h : c.penultimate ∈ c.support.dropLast :=
      SimpleGraph.Walk.penultimate_mem_dropLast_support hcnil
    rw [← SimpleGraph.Walk.support_dropLast hcnil] at h
    rw [← SimpleGraph.Walk.support_dropLast_concat hcnil]
    exact List.mem_append_left _ h
  have hxpen : G.Adj c.penultimate x := (hadj c.penultimate hpen_supp).symm
  have hxdrop : x ∉ c.dropLast.support := by
    intro hmem
    exact hx (by
      rw [← SimpleGraph.Walk.support_dropLast_concat hcnil]
      exact List.mem_append_left _ hmem)
  -- splice `x` into the cycle: `x → u → … → penultimate → x`
  have hqpath : (c.dropLast.concat hxpen).IsPath := hc.isPath_dropLast.concat hxdrop hxpen
  have hqlen : (c.dropLast.concat hxpen).length = c.length := by
    rw [SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_dropLast]
    have h3 : 3 ≤ c.length := hc.three_le_length
    omega
  have hcyc : (SimpleGraph.Walk.cons hxu (c.dropLast.concat hxpen)).IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · simpa using hqpath
    · rw [SimpleGraph.Walk.length_cons, hqlen]
      have h3 : 3 ≤ c.length := hc.three_le_length
      omega
  -- it is strictly longer than the longest cycle `c`
  have hlong := hlc.2 x (SimpleGraph.Walk.cons hxu (c.dropLast.concat hxpen)) hcyc
  rw [SimpleGraph.Walk.length_cons, hqlen] at hlong
  omega

/-- Usable form: a longest cycle of a 3-connected graph with exactly one vertex off it has a
chord. -/
theorem hasChord_of_one_off (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsKConnected G 3) {u : V} {c : G.Walk u u} (hlc : IsLongestCycle c) {x : V}
    (hx : x ∉ c.support) (honly : ∀ y : V, y ∉ c.support → y = x) : HasChord c := by
  classical
  by_contra hno
  refine one_off_no_chordless_longest G hG hlc ?_ hx honly
  intro e he
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.Walk.isChord_sym2Mk] at he
    exact hno ⟨a, b, he.1, he.2.2.1, he.2.2.2, he.2.1⟩

omit [Fintype V] in

/-- The four-way exhaustive case split: spanning cycles, one vertex off the cycle, and at least two
vertices off the cycle split by whether the off-cycle vertices induce a connected graph. -/
theorem main : H1 → H2 → type_of% @OMA.S_opg_chords_of_longest_cycles.main := by
  intro h1 h2 V _ G hG u c hlc
  classical
  by_cases hspan : ∀ v : V, v ∈ c.support
  · exact hasChord_of_spanning_isCycle G u c hlc.1 hspan (fun v => min_degree_three G hG v)
  · have hoff : ∃ v : V, v ∉ c.support := by
      by_contra hcon
      exact hspan fun v => by
        by_contra hv
        exact hcon ⟨v, hv⟩
    by_cases htwo : ∃ v w : V, v ≠ w ∧ v ∉ c.support ∧ w ∉ c.support
    · by_cases hconn : (G.induce {v : V | v ∉ c.support}).Connected
      · exact h1 V G hG u c hlc hoff htwo hconn
      · exact h2 V G hG u c hlc hoff hconn
    · obtain ⟨x, hx⟩ := hoff
      exact hasChord_of_one_off G hG hlc hx (fun y hy => by
        by_contra hne
        exact htwo ⟨y, x, hne, hy, hx⟩)

end OneOff

end OMA.R_opg_chords_of_longest_cycles_R4
