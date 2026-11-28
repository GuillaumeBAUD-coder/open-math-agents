import Mathlib

/-!
# List colorings of edge-critical graphs

Source: https://www.openproblemgarden.org/op/list_colorings_of_edge_critical_graphs
Credit: @Moti1125

Conjecture: suppose that `G` is a `Δ`-edge-critical graph. Suppose that for each edge `e` of `G`
there is a list `L(e)` of `Δ` colors. Then `G` is `L`-edge-colorable unless all lists are equal
to each other.

From the source: a graph `G` is `Δ`-edge-critical if it is not `Δ`-edge-colorable but every
edge-deleted subgraph is `Δ`-edge-colorable, where `Δ` is the maximum degree of `G`.

Conventions:
- Graphs are finite simple graphs on `Fin n`.
- An edge colouring is a colouring of the line graph `G.lineGraph`, whose vertices are the edges
  of `G`, two edges being adjacent when they share an endpoint. So `G` is `k`-edge-colorable iff
  `G.lineGraph.Colorable k`.
- In "every edge-deleted subgraph is `Δ`-edge-colorable", `Δ` is the maximum degree of `G`
  itself, as in the source's definition.
- Colours are natural numbers; a list is a `Finset ℕ` with exactly `Δ` elements. Any finite
  supply of colours can be relabelled into `ℕ`.
- `G` is `L`-edge-colorable if there is a proper edge colouring `c` with `c e ∈ L e` for every
  edge `e`.
-/

namespace OMA.S_opg_list_colorings_of_edge_critical_graphs

open scoped Classical in
theorem main :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ¬ G.lineGraph.Colorable G.maxDegree →
      (∀ e ∈ G.edgeSet, (G.deleteEdges {e}).lineGraph.Colorable G.maxDegree) →
      ∀ L : G.edgeSet → Finset ℕ, (∀ e, (L e).card = G.maxDegree) →
        (∃ e e', L e ≠ L e') →
        ∃ c : G.edgeSet → ℕ, (∀ e, c e ∈ L e) ∧ ∀ e e', G.lineGraph.Adj e e' → c e ≠ c e' := by
  sorry

end OMA.S_opg_list_colorings_of_edge_critical_graphs
