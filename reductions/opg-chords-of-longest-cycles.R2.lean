import OMAStatements.S_opg_chords_of_longest_cycles
import Mathlib.Tactic

/-!
# Reduction R2 of Thomassen's chord conjecture (opg-chords-of-longest-cycles)

Target: every longest cycle of a 3-connected finite simple graph has a chord
(Open Problem Garden, C. Thomassen). It is still OPEN in this strong form (every longest cycle):
Thomassen, JCTB 179 (2026) 90-117, proves only that some longest cycle has a chord; the known
classes with the strong form are 2-connected cubic graphs (Thomassen, JCTB 129 (2018) 148-157),
planar graphs of minimum degree 4 (Zhang 1987), the projective plane (Li-Zhang 2003), the torus
and the Klein bottle at connectivity 4 (Li-Zhang 2003), and graphs of large minimum degree
(Harvey, EJC 2017). The remaining gap is 3-connected graphs of minimum degree 3.

Unlike R1, this reduction PROVES the easy Hamiltonian case in the file itself:

* `card_ge_four` and `min_degree`: a 3-connected graph has at least four vertices and minimum
  degree at least 3. (`min_degree` is the reusable piece: for a vertex `v` of degree at most 2,
  delete its neighbour set and `v` becomes isolated in a graph that 3-connectivity requires to be
  connected, so that graph is a single vertex and the whole graph has at most 3 vertices.)
* `hamiltonian_hasChord`: a longest cycle that visits every vertex has a chord. If it had none,
  every edge of the graph would be an edge of the cycle (no chord can leave the cycle, and the
  cycle covers all vertices), hence `#E = c.length`; but a cycle visits a vertex only twice, so
  the handshake formula `sum of degrees = 2#E <= 2 c.length` contradicts `minimum degree >= 3`.

What remains, and is left as the two hypotheses, is exactly the non-Hamiltonian case, split by
whether the vertices off the cycle induce one bridge (`H1`) or at least two bridges (`H2`); these
are the cases the published proofs handle separately, and `main` is their exhaustive case split.
-/

namespace OMA.R_opg_chords_of_longest_cycles_R2

open OMA.S_opg_chords_of_longest_cycles

/-- The chord conjecture for a longest cycle that is not spanning, when the vertices off the
cycle induce a connected graph (a single bridge of the cycle). -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsKConnected G 3 →
    ∀ (u : V) (c : G.Walk u u), IsLongestCycle c → (∃ v : V, v ∉ c.support) →
      (G.induce {v : V | v ∉ c.support}).Connected → HasChord c

/-- The chord conjecture for a longest cycle that is not spanning, when the vertices off the
cycle induce a disconnected graph (at least two bridges of the cycle). -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsKConnected G 3 →
    ∀ (u : V) (c : G.Walk u u), IsLongestCycle c → (∃ v : V, v ∉ c.support) →
      ¬ (G.induce {v : V | v ∉ c.support}).Connected → HasChord c

variable {V : Type} [Fintype V]

/-- Deleting at most two vertices of a 3-connected graph leaves a nonempty connected graph, so a
3-connected graph has more than three vertices. -/
lemma card_ge_four {G : SimpleGraph V} (hG : IsKConnected G 3) : 4 ≤ Fintype.card V := by
  have h := hG.1
  omega

/-- A 3-connected graph has minimum degree at least 3. -/
lemma min_degree {G : SimpleGraph V} [DecidableRel G.Adj] (hG : IsKConnected G 3) (v : V) :
    3 ≤ G.degree v := by
  classical
  by_contra hlt
  have hle : G.degree v ≤ 2 := by omega
  have hdeg : G.degree v = (G.neighborFinset v).card := rfl
  have hScard : (G.neighborFinset v).card < 3 := by omega
  have hconn : (G.induce (↑(G.neighborFinset v) : Set V)ᶜ).Connected := hG.2 _ hScard
  have hvS : v ∉ G.neighborFinset v := by simp
  have hv' : v ∈ (↑(G.neighborFinset v) : Set V)ᶜ := by simpa using hvS
  -- the vertex v is isolated in the graph induced on the complement of its neighbour set
  have hiso : (G.induce (↑(G.neighborFinset v) : Set V)ᶜ).neighborSet ⟨v, hv'⟩ = ∅ := by
    ext x
    simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
    intro hadj
    have hmem : (x : V) ∈ G.neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]
      exact SimpleGraph.induce_adj.mp hadj
    exact x.2 hmem
  -- hence every vertex of that complement is v
  have hall : ∀ w : V, w ∉ G.neighborFinset v → w = v := by
    intro w hw
    by_contra hne
    have hw' : w ∈ (↑(G.neighborFinset v) : Set V)ᶜ := by simpa using hw
    have hne' : (⟨v, hv'⟩ : ↥((↑(G.neighborFinset v) : Set V)ᶜ)) ≠ ⟨w, hw'⟩ := by
      intro h
      exact hne (congrArg Subtype.val h).symm
    exact (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty hne' hiso)
      (hconn.preconnected ⟨v, hv'⟩ ⟨w, hw'⟩)
  -- so the whole vertex set is the neighbour set of v plus v itself
  have hsub : (Finset.univ : Finset V) ⊆ insert v (G.neighborFinset v) := by
    intro w _
    by_cases hw : w ∈ G.neighborFinset v
    · exact Finset.mem_insert_of_mem hw
    · rw [hall w hw]
      exact Finset.mem_insert_self v _
  have h1 : Fintype.card V ≤ (insert v (G.neighborFinset v)).card := Finset.card_le_card hsub
  have h2 : (insert v (G.neighborFinset v)).card ≤ (G.neighborFinset v).card + 1 :=
    Finset.card_insert_le v _
  have h3 := hG.1
  omega

/-- A longest cycle that visits every vertex has a chord. -/
lemma hamiltonian_hasChord {G : SimpleGraph V} [DecidableRel G.Adj] (hG : IsKConnected G 3) {u : V}
    {c : G.Walk u u} (hc : c.IsCycle) (hspan : ∀ v : V, v ∈ c.support) : HasChord c := by
  classical
  by_contra hno
  have hch : c.IsChordless := by
    rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges]
    intro a b ha hb hab
    by_contra hne
    exact hno ⟨a, b, hab, ha, hb, hne⟩
  -- without a chord, every edge of the graph is an edge of the cycle
  have hedge : G.edgeFinset ⊆ c.edges.toFinset := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      have hset : s(x, y) ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp he
      have hadj : G.Adj x y := (SimpleGraph.mem_edgeSet G).mp hset
      have hmem : s(x, y) ∈ c.edges := hch.mem_edges (hspan x) (hspan y) hadj
      simpa using hmem
  have hE : G.edgeFinset.card ≤ c.length := by
    have h1 : G.edgeFinset.card ≤ c.edges.toFinset.card := Finset.card_le_card hedge
    have h2 : c.edges.toFinset.card = c.edges.length := List.toFinset_card_of_nodup hc.edges_nodup
    have h3 : c.edges.length = c.length := c.length_edges
    omega
  have hL : c.length ≤ Fintype.card V := by
    have hnod : c.support.tail.Nodup := hc.support_nodup
    have hlen : c.support.tail.length = c.length := by
      have h := List.length_tail (l := c.support)
      rw [SimpleGraph.Walk.length_support] at h
      omega
    have hcard : c.support.tail.toFinset.card = c.support.tail.length :=
      List.toFinset_card_of_nodup hnod
    have hle : c.support.tail.toFinset.card ≤ Fintype.card V := by
      have h := Finset.card_le_card (Finset.subset_univ c.support.tail.toFinset)
      simpa using h
    omega
  -- handshake: the degree sum is twice the number of edges, but at least 3 per vertex
  have hhand : ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hlow : 3 * Fintype.card V ≤ ∑ v : V, G.degree v := by
    have h := Finset.card_nsmul_le_sum (s := Finset.univ) (f := fun v : V => G.degree v)
      (n := 3) (fun v _ => min_degree hG v)
    have h' : Fintype.card V * 3 ≤ ∑ v : V, G.degree v := by
      simpa [Finset.card_univ] using h
    omega
  have hup : ∑ v : V, G.degree v ≤ 2 * Fintype.card V := by
    rw [hhand]
    omega
  have hcard := card_ge_four hG
  omega

theorem main : H1 → H2 → type_of% @OMA.S_opg_chords_of_longest_cycles.main := by
  intro h1 h2 V _ G hG u c hc
  classical
  by_cases hspan : ∀ v : V, v ∈ c.support
  · exact hamiltonian_hasChord hG hc.1 hspan
  · have hoff : ∃ v : V, v ∉ c.support := by
      by_contra hcon
      exact hspan fun v => by
        by_contra hv
        exact hcon ⟨v, hv⟩
    by_cases hconn : (G.induce {v : V | v ∉ c.support}).Connected
    · exact h1 V G hG u c hc hoff hconn
    · exact h2 V G hG u c hc hoff hconn

end OMA.R_opg_chords_of_longest_cycles_R2
