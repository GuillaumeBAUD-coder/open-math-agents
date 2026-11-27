import Mathlib

/-!
# Kriesell's Conjecture

Source: https://www.openproblemgarden.org/op/kriesells_conjecture
Credit: @lzvxck

The source: let `G` be a graph and let `T ⊆ V(G)` such that for any pair `u, v ∈ T` there are
`2k` edge-disjoint paths from `u` to `v` in `G`. Then `G` contains `k` edge-disjoint trees,
each of which contains `T`.

Conventions: graphs are finite and simple, `u ≠ v` in the hypothesis, and a tree of `G` is a
subgraph of `G` which is a tree. Restricting to simple graphs loses nothing: subdividing every
edge of a multigraph preserves both the number of edge-disjoint paths between original
vertices and the existence of `k` edge-disjoint trees containing `T` (a path between vertices
of `T` inside such a tree uses both halves of each subdivided edge it meets).
-/

namespace OMA.S_opg_kriesells_conjecture

/-- There are `n` pairwise edge-disjoint paths from `u` to `v` in `G`. -/
def HasEdgeDisjointPaths {V : Type*} (G : SimpleGraph V) (u v : V) (n : ℕ) : Prop :=
  ∃ p : Fin n → G.Walk u v, (∀ i, (p i).IsPath) ∧
    ∀ i j, i ≠ j → ∀ e ∈ (p i).edges, e ∉ (p j).edges

/-- **Kriesell's conjecture.** If any two distinct vertices of `T` are joined by `2k`
edge-disjoint paths in `G`, then `G` contains `k` edge-disjoint trees each containing `T`. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (T : Set V) (k : ℕ),
    (∀ u ∈ T, ∀ v ∈ T, u ≠ v → HasEdgeDisjointPaths G u v (2 * k)) →
      ∃ H : Fin k → G.Subgraph,
        (∀ i, (H i).coe.IsTree) ∧ (∀ i, T ⊆ (H i).verts) ∧
        ∀ i j, i ≠ j → Disjoint (H i).edgeSet (H j).edgeSet := by
  sorry

end OMA.S_opg_kriesells_conjecture
