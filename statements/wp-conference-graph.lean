import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# Conference graph existence problem

Does there exist a conference graph on `v` vertices for every integer `v > 1` such that
`v ≡ 1 [MOD 4]` and `v` is an odd sum of two squares?

A conference graph on `v` vertices is a strongly regular graph with parameters
`(v, (v - 1) / 2, (v - 5) / 4, (v - 1) / 4)`.

*Reference:* https://en.wikipedia.org/wiki/Conference_graph
-/

namespace OMA.S_wp_conference_graph

/-- A simple graph on `v` vertices is a conference graph if it is strongly regular with
parameters `(v, (v - 1) / 2, (v - 5) / 4, (v - 1) / 4)`. -/
def IsConferenceGraph {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : ℕ) : Prop :=
  G.IsSRGWith v ((v - 1) / 2) ((v - 5) / 4) ((v - 1) / 4)

/-- Every integer `v > 1` with `v ≡ 1 [MOD 4]` that is a sum of two squares is the order
of a conference graph. -/
theorem main :
    ∀ v : ℕ, 1 < v → v % 4 = 1 → (∃ a b : ℕ, v = a ^ 2 + b ^ 2) →
      ∃ (G : SimpleGraph (Fin v)) (_ : DecidableRel G.Adj), IsConferenceGraph G v := by
  sorry

end OMA.S_wp_conference_graph
