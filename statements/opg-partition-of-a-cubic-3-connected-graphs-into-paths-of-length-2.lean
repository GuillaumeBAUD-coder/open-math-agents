import Mathlib

/-!
# Partition of a cubic 3-connected graph into paths of length 2

Source: https://www.openproblemgarden.org/op/partition_of_a_cubic_3_connected_graphs_into_paths_of_length_2
Credit: @ishaanzee

**Problem** (A. Kelmans). Does every 3-connected cubic graph on `3k` vertices admit a partition into
`k` paths of length 2?

(Kelmans constructed infinitely many 2-connected cubic graphs for which this fails.) We state the
affirmative answer.

Formalization:
* Graphs are finite simple graphs; cubic is `IsRegularOfDegree 3`; 3-connected (vertex
  connectivity): more than 3 vertices, and connected after deleting any set of fewer than 3
  vertices.
* A partition of the vertices into `k` paths of length 2 is a map `f : V → Fin k` whose fibres all
  have exactly 3 vertices, each fibre containing a vertex (the middle of the path) adjacent to the
  other two vertices of the fibre.
-/

namespace OMA.S_opg_partition_of_a_cubic_3_connected_graphs_into_paths_of_length_2

/-- `G` is `k`-connected: it has more than `k` vertices and stays connected after deleting any
fewer than `k` vertices. -/
def IsKConnected {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Nat.card V ∧ ∀ S : Set V, S.Finite → S.ncard < k → (G.induce Sᶜ).Connected

/-- **Kelmans' problem**, affirmative form. -/
theorem main : ∀ (k : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], G.IsRegularOfDegree 3 → IsKConnected G 3 → Fintype.card V = 3 * k →
      ∃ f : V → Fin k, (∀ i, (Finset.univ.filter fun v => f v = i).card = 3) ∧
        ∀ i, ∃ b, f b = i ∧ ∀ a, f a = i → a ≠ b → G.Adj a b := by
  sorry

end OMA.S_opg_partition_of_a_cubic_3_connected_graphs_into_paths_of_length_2
