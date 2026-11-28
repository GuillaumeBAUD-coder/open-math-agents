import OMAStatements.S_opg_57_regular_moore_graph

-- Reduction opg-57-regular-moore-graph.R1 of 57-regular Moore graph?
-- Credit: @MBimrose
--
-- The target asks for a finite graph that is 57-regular, of (extended) diameter 2 and (extended)
-- girth 5.  With Mathlib's definitions (`SimpleGraph.ediam` is `⊤` on a disconnected graph,
-- `SimpleGraph.egirth` is `⊤` on an acyclic graph) such a graph is exactly a (57,2)-Moore graph on
-- `1 + 57 + 57 * 56 = 3250` vertices, i.e. the open Hoffman-Singleton case k = 57.
--
-- This reduction separates the two independent halves:
--   * H1 is the open combinatorial content, stated with NO diameter/girth/regularity API at all:
--     a graph on `Fin 3250` in which every vertex has exactly 57 neighbours, with no triangle and
--     no 4-cycle (an explicit edge set of a (3250,57,0,1) strongly regular graph would do).
--   * H2 is pure Mathlib plumbing: any such graph has extended diameter 2 and extended girth 5.
--     It is provable (Moore-bound counting: the 57 * 56 two-step walks out of a vertex inject into
--     the 3250 - 58 remaining vertices, so every non-neighbour of a vertex is at distance 2 and a
--     5-cycle exists), and it is attacked separately as the step opg-57-regular-moore-graph.R1.H2.

namespace OMA.R_opg_57_regular_moore_graph_R1

/-- Open content: a graph on 3250 vertices in which every vertex has exactly 57 neighbours, with no
triangle and no 4-cycle.  Equivalently: the edge set of a (3250,57,0,1) strongly regular graph. -/
def H1 : Prop :=
  ∃ G : SimpleGraph (Fin 3250),
    (∀ v : Fin 3250, Nat.card { w : Fin 3250 // G.Adj v w } = 57) ∧
    (∀ a b c : Fin 3250, G.Adj a b → G.Adj b c → ¬ G.Adj c a) ∧
    (∀ a b c d : Fin 3250, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)

/-- Mathlib plumbing: every graph on 3250 vertices with the H1 properties has extended diameter 2
and extended girth 5.  (Provable; it is the Moore bound counting argument.) -/
def H2 : Prop :=
  ∀ G : SimpleGraph (Fin 3250),
    (∀ v : Fin 3250, Nat.card { w : Fin 3250 // G.Adj v w } = 57) →
    (∀ a b c : Fin 3250, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
    (∀ a b c d : Fin 3250, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
    G.ediam = 2 ∧ G.egirth = 5

theorem main : H1 → H2 → type_of% @OMA.S_opg_57_regular_moore_graph.main := by
  intro h1 h2
  obtain ⟨G, hdeg, htri, hc4⟩ := h1
  haveI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨hdiam, hgirth⟩ := h2 G hdeg htri hc4
  refine ⟨Fin 3250, inferInstance, G, inferInstance, ?_, hdiam, hgirth⟩
  intro v
  have hcard : (G.neighborFinset v).card = Nat.card { w : Fin 3250 // G.Adj v w } := by
    rw [SimpleGraph.neighborFinset_eq_filter,
      ← Fintype.card_subtype (fun w : Fin 3250 => G.Adj v w), ← Nat.card_eq_fintype_card]
  show (G.neighborFinset v).card = 57
  rw [hcard]
  exact hdeg v

end OMA.R_opg_57_regular_moore_graph_R1
