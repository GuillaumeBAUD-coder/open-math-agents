import Mathlib

/-!
# Decomposing a connected graph into paths.

Source: https://www.openproblemgarden.org/op/decomposing_a_connected_graph_into_paths
Credit: @joshuadc11

Gallai's conjecture: every simple connected graph on `n` vertices can be decomposed into at most
`(n + 1) / 2` paths.

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s; connected is `G.Connected` (which also ensures `V` is
  nonempty).
* A path in `G` is a `G.Walk u v` satisfying `walk.IsPath` (no repeated vertices, hence no repeated
  edges).
* A decomposition of `G` into `k` paths is an edge-decomposition: a family `P : Fin k → PathIn G`
  such that every edge in `G.edgeSet` belongs to `(P i).walk.edges` for a unique `i : Fin k`.
* Since `k : ℕ`, the bound `k ≤ (n + 1) / 2` (equivalently `2 * k ≤ n + 1`) expresses at most
  `1/2 (n + 1)` paths.
-/

namespace OMA.S_opg_decomposing_a_connected_graph_into_paths

/-- A simple path in a graph `G`, bundled with its endpoints. -/
structure PathIn {V : Type} (G : SimpleGraph V) where
  u : V
  v : V
  walk : G.Walk u v
  isPath : walk.IsPath

/-- `G` admits an edge-decomposition into `k` paths. -/
def HasPathDecomposition {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ P : Fin k → PathIn G, ∀ e ∈ G.edgeSet, ∃! i : Fin k, e ∈ (P i).walk.edges

/-- Every simple connected graph on `n` vertices can be edge-decomposed into at most
`(n + 1) / 2` paths. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
    ∃ k : ℕ, 2 * k ≤ Fintype.card V + 1 ∧ HasPathDecomposition G k := by
  sorry

end OMA.S_opg_decomposing_a_connected_graph_into_paths
