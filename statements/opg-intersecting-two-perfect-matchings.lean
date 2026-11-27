import Mathlib

/-!
# The intersection of two perfect matchings

Source: https://www.openproblemgarden.org/op/intersecting_two_perfect_matchings
Credit: @ishaanzee

**Conjecture** (E. Máčajová, M. Škoviera). Every bridgeless cubic graph has two perfect matchings
`M₁`, `M₂` so that `M₁ ∩ M₂` does not contain an odd edge-cut.

Formalization:
* Graphs are finite simple graphs (`SimpleGraph`); cubic means 3-regular, and bridgeless means
  no edge is a bridge (`SimpleGraph.IsBridge`). (The source works with cubic graphs in general;
  this statement covers the simple ones.)
* Perfect matchings are Mathlib's `Subgraph.IsPerfectMatching`; `M₁ ∩ M₂` is the intersection of
  their edge sets.
* The edge-cut of a vertex set `X` is the set of edges with exactly one end in `X`; it is odd
  when it has an odd number of edges. `M₁ ∩ M₂` contains an odd edge-cut if some odd edge-cut is
  a subset of `M₁ ∩ M₂`.
-/

namespace OMA.S_opg_intersecting_two_perfect_matchings

/-- The edge-cut `δ(X)`: edges of `G` with exactly one end in `X`. -/
def edgeCut {V : Type*} (G : SimpleGraph V) (X : Set V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ ∃ u v, e = s(u, v) ∧ u ∈ X ∧ v ∉ X}

/-- **Máčajová–Škoviera conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsRegularOfDegree 3 → (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) →
      ∃ M₁ M₂ : G.Subgraph, M₁.IsPerfectMatching ∧ M₂.IsPerfectMatching ∧
        ∀ X : Set V, Odd (edgeCut G X).ncard → ¬ edgeCut G X ⊆ M₁.edgeSet ∩ M₂.edgeSet := by
  sorry

end OMA.S_opg_intersecting_two_perfect_matchings
