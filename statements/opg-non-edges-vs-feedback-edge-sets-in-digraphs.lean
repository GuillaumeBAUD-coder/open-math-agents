import Mathlib

/-!
# Non-edges vs. feedback edge sets in digraphs

Source: https://www.openproblemgarden.org/op/non_edges_vs_feedback_edge_sets_in_digraphs
Credit: @shc261392

For a simple digraph `G`, let `γ(G)` be the number of unordered pairs of nonadjacent vertices
(non-edges) and `β(G)` the size of the smallest feedback edge set (a set of arcs whose deletion
leaves no directed cycle).

Conjecture (Chudnovsky, Seymour and Sullivan): if `G` is a simple digraph without directed cycles
of length at most `3`, then `β(G) ≤ γ(G) / 2`.

Reading used here:
* A simple digraph is a relation `D : V → V → Prop` on a finite type `V`. Having no directed
  cycle of length `1`, `2` or `3` means: no loop, no pair of opposite arcs, no directed triangle.
* A non-edge is a pair `{u, v}` (an element of `Sym2 V`) with `u ≠ v` and no arc between `u` and
  `v` in either direction.
* `β(G) ≤ γ(G) / 2` says that some feedback edge set `F` (a set of arcs of `D` such that
  `D` minus `F` has no directed cycle, i.e. no vertex reaches itself by a nonempty path) has
  `2 * |F| ≤ γ(G)`.
-/

namespace OMA.S_opg_non_edges_vs_feedback_edge_sets_in_digraphs

/-- The number of non-edges of `D`: unordered pairs of distinct vertices with no arc between. -/
noncomputable def nonEdges {V : Type} (D : V → V → Prop) : ℕ :=
  {s : Sym2 V | ¬ s.IsDiag ∧ ∀ u v, s = s(u, v) → ¬ D u v}.ncard

theorem main :
    ∀ (V : Type) [Fintype V] (D : V → V → Prop),
      (∀ a, ¬ D a a) → (∀ a b, D a b → ¬ D b a) → (∀ a b c, D a b → D b c → ¬ D c a) →
        ∃ F : Set (V × V), (∀ p ∈ F, D p.1 p.2) ∧ 2 * F.ncard ≤ nonEdges D ∧
          ∀ v, ¬ Relation.TransGen (fun a b => D a b ∧ (a, b) ∉ F) v v := by
  sorry

end OMA.S_opg_non_edges_vs_feedback_edge_sets_in_digraphs
