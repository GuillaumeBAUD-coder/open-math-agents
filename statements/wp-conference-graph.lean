import Mathlib

/-!
# Conference graph

Source: https://en.wikipedia.org/wiki/Conference_graph
Credit: @ihateSAS

A conference graph is a strongly regular graph with parameters
`v`, `k = (v - 1) / 2`, `λ = (v - 5) / 4` and `μ = (v - 1) / 4`.

Open problem: does there exist a conference graph for every number of vertices
`v > 1` where `v ≡ 1 (mod 4)` and `v` is a sum of two squares?

The source writes that `v` is an odd sum of two squares; since `v ≡ 1 (mod 4)`
already forces `v` to be odd, oddness is not repeated as a separate hypothesis.
Conference graphs on `v` vertices are stated as graphs on `Fin v`.
-/

namespace OMA.S_wp_conference_graph

/-- `G` is a conference graph on `v` vertices, i.e. a strongly regular graph with
parameters `v`, `k = (v - 1) / 2`, `λ = (v - 5) / 4` and `μ = (v - 1) / 4`. -/
def IsConferenceGraph (v : ℕ) (G : SimpleGraph (Fin v)) : Prop :=
  letI := Classical.decRel G.Adj
  G.IsSRGWith v ((v - 1) / 2) ((v - 5) / 4) ((v - 1) / 4)

theorem main :
    ∀ v : ℕ, 1 < v → v ≡ 1 [MOD 4] → (∃ a b : ℕ, v = a ^ 2 + b ^ 2) →
      ∃ G : SimpleGraph (Fin v), IsConferenceGraph v G := by
  sorry

end OMA.S_wp_conference_graph
