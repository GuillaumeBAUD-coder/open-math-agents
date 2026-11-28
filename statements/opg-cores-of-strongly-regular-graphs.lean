import Mathlib

/-!
# Cores of strongly regular graphs

Source: https://www.openproblemgarden.org/op/cores_of_strongly_regular_graphs
Credit: @joshuadc11

Cameron–Kazanidis question: does every finite strongly regular graph have either itself or a
complete graph as its core?

## Encoding

* Strongly regular graphs use Mathlib's `SimpleGraph.IsSRGWith n k ℓ μ`.
* A finite graph `G` is its own core iff every graph endomorphism `f : G →g G` is bijective.
* Since every complete graph `K_m` is a core and the core of a finite graph is unique up to
  isomorphism, `G` has `K_m` as its core iff `G` is homomorphically equivalent to
  `SimpleGraph.completeGraph (Fin m)` (i.e., homomorphisms exist in both directions).
* The source asks a yes/no question without conjecturing an answer; `main` states the answer yes,
  and a disproof would answer no.
-/

namespace OMA.S_opg_cores_of_strongly_regular_graphs

/-- Every finite strongly regular graph is either a core (every endomorphism is bijective) or
homomorphically equivalent to a complete graph `K_m`. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (n k ℓ μ : ℕ),
    G.IsSRGWith n k ℓ μ →
    (∀ f : G →g G, Function.Bijective f) ∨
    (∃ m : ℕ, Nonempty (G →g SimpleGraph.completeGraph (Fin m)) ∧
      Nonempty (SimpleGraph.completeGraph (Fin m) →g G)) := by
  sorry

end OMA.S_opg_cores_of_strongly_regular_graphs
