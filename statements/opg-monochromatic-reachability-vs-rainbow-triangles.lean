import Mathlib

/-!
# Monochromatic reachability or rainbow triangles

Source: https://www.openproblemgarden.org/op/monochromatic_reachability_vs_rainbow_triangles
(raised by B. Sands, N. Sauer, R. Woodrow)
Credit: @ishaanzee

In an edge-colored digraph, a subgraph is rainbow if all its edges have distinct colors, and
monochromatic if all its edges have the same color.

**Problem.** Let `G` be a tournament with edges colored from a set of three colors. Is it true that
`G` must have either a rainbow directed cycle of length three or a vertex `v` so that every other
vertex can be reached from `v` by a monochromatic (directed) path?

(Sands, Sauer and Woodrow proved that every 2-edge-colored tournament has such a vertex.) We state
the affirmative answer.

Formalization: a tournament on a finite set `V` is a relation `T` with no loops and exactly one of
`T u v`, `T v u` for distinct `u`, `v`. An edge coloring is `c : V → V → Fin 3` (`c u v` is the
color of the arc `u → v`). A monochromatic directed path of color `k` from `v` to `w` exists iff
`w` is reachable from `v` in the digraph of arcs of color `k` (`Relation.TransGen`).
-/

namespace OMA.S_opg_monochromatic_reachability_vs_rainbow_triangles

/-- **Sands–Sauer–Woodrow problem**, affirmative form. -/
theorem main : ∀ (V : Type) [Fintype V] [Nonempty V] (T : V → V → Prop) (c : V → V → Fin 3),
    (∀ v, ¬ T v v) → (∀ u v, u ≠ v → (T u v ↔ ¬ T v u)) →
      (∃ a b d : V, T a b ∧ T b d ∧ T d a ∧
          c a b ≠ c b d ∧ c b d ≠ c d a ∧ c a b ≠ c d a) ∨
      ∃ v : V, ∀ w : V, w ≠ v → ∃ k : Fin 3,
        Relation.TransGen (fun x y => T x y ∧ c x y = k) v w := by
  sorry

end OMA.S_opg_monochromatic_reachability_vs_rainbow_triangles
