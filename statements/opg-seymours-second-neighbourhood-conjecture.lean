import Mathlib

/-!
# Seymour's Second Neighbourhood Conjecture

Source: https://www.openproblemgarden.org/op/seymours_second_neighbourhood_conjecture
Credit: @biondadave

Conjecture (Seymour): Any oriented graph has a vertex whose outdegree is at most its second
outdegree. The `n`-th outdegree of `v` is the number of vertices `w` for which the shortest
directed path from `v` to `w` has length `n`.

Conventions:
- An oriented graph is a finite directed graph with no loops and no pair of opposite arcs (no
  directed 2-cycles). It is a Mathlib `Digraph V` with `V` finite and those two hypotheses.
  Parallel arcs cannot occur in a `Digraph`.
- The graph is nonempty, since the conclusion asks for a vertex.
- First out-neighbourhood of `v`: the `w` with `G.Adj v w` (shortest path length `1`).
- Second out-neighbourhood of `v`: the `w ≠ v` that are not out-neighbours of `v` but are reached
  by a directed path `v → u → w` (shortest path length exactly `2`).
-/

namespace OMA.S_opg_seymours_second_neighbourhood_conjecture

theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj],
      (∀ v, ¬ G.Adj v v) → (∀ u v, G.Adj u v → ¬ G.Adj v u) →
      ∃ v : V, (Finset.univ.filter (fun w => G.Adj v w)).card ≤
        (Finset.univ.filter (fun w => w ≠ v ∧ ¬ G.Adj v w ∧ ∃ u, G.Adj v u ∧ G.Adj u w)).card := by
  sorry

end OMA.S_opg_seymours_second_neighbourhood_conjecture
