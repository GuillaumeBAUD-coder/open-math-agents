import Mathlib

/-!
# Seymour's Second Neighbourhood Conjecture

Source: https://www.openproblemgarden.org/op/seymours_second_neighbourhood_conjecture
Credit: @lzvxck

The source: any oriented graph has a vertex whose outdegree is at most its second outdegree.
The `i`-th outdegree of `v` is the number of vertices `w` for which the minimal
outward-directed path from `v` to `w` has length `i`.

An oriented graph is a finite directed graph with no loops and no pair of opposite arcs
(no 2-cycles). It is modelled by an arc relation `G.Adj` on a finite, nonempty vertex type
(the empty graph has no vertex, so the statement is about nonempty graphs).
-/

namespace OMA.S_opg_seymours_second_neighbourhood_conjecture

/-- `G` is an oriented graph: no loops and no pair of opposite arcs. -/
def IsOriented {V : Type*} (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ ∀ u v, G.Adj u v → ¬ G.Adj v u

/-- The first out-neighbourhood of `v`: vertices `w` with an arc `v → w`, i.e. those whose
minimal outward path from `v` has length 1. -/
def outNbhd {V : Type*} (G : Digraph V) (v : V) : Set V :=
  {w | G.Adj v w}

/-- The second out-neighbourhood of `v`: vertices `w` whose minimal outward-directed path from
`v` has length exactly 2, i.e. `w ≠ v`, there is no arc `v → w`, and there is `u` with arcs
`v → u → w`. -/
def secondOutNbhd {V : Type*} (G : Digraph V) (v : V) : Set V :=
  {w | w ≠ v ∧ ¬ G.Adj v w ∧ ∃ u, G.Adj v u ∧ G.Adj u w}

/-- **Seymour's Second Neighbourhood Conjecture.** Every finite nonempty oriented graph has a
vertex whose outdegree is at most its second outdegree. -/
theorem main : ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V), IsOriented G →
    ∃ v : V, (outNbhd G v).ncard ≤ (secondOutNbhd G v).ncard := by
  sorry

end OMA.S_opg_seymours_second_neighbourhood_conjecture
