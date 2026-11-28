import Mathlib

/-!
# Decomposing a connected graph into paths

Source: https://www.openproblemgarden.org/op/decomposing_a_connected_graph_into_paths
Conjecture of Gallai: every simple connected graph on `n` vertices can be decomposed into at
most `(n + 1) / 2` paths, that is, its vertex set can be partitioned into at most that many
parts, each of which is the vertex set of a path of the graph.

The bound is written in the equivalent integer form `2 * k ≤ n + 1`.
-/

namespace OMA.S_opg_decomposing_a_connected_graph_into_paths

/-- The vertex set of `G` is partitioned into the parts `parts i`, each of which is the vertex
set of a path of `G`. -/
def IsPathDecomposition {V : Type*} (G : SimpleGraph V) (k : ℕ) (parts : Fin k → Set V) : Prop :=
  (∀ i : Fin k, ∃ u v : V, ∃ p : G.Path u v,
    ∀ x : V, x ∈ (p : G.Walk u v).support ↔ x ∈ parts i) ∧
    ∀ x : V, ∃! i : Fin k, x ∈ parts i

/-- Gallai's conjecture: every simple connected graph on `n` vertices has its vertices
decomposed into at most `(n + 1) / 2` paths. -/
theorem main : ∀ {V : Type*} [Fintype V] (G : SimpleGraph V), G.Connected →
    ∃ (k : ℕ) (parts : Fin k → Set V),
      2 * k ≤ Fintype.card V + 1 ∧ IsPathDecomposition G k parts := by
  sorry

end OMA.S_opg_decomposing_a_connected_graph_into_paths
