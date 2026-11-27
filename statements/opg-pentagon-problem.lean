import Mathlib

/-!
# Pentagon problem

Source: https://www.openproblemgarden.org/op/pentagon_problem
Credit: @joshuadc11

Nešetřil's Pentagon problem: let `G` be a 3-regular graph that contains no cycle of length shorter
than `g`. Is it true that for large enough `g`, there is a graph homomorphism `G → C₅`?

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s; 3-regular is `G.IsRegularOfDegree 3`.
* Containing no cycle of length shorter than `g` is stated directly as
  `∀ (v : V) (p : G.Walk v v), p.IsCycle → g ≤ p.length`.
* `C₅` is Mathlib's `SimpleGraph.cycleGraph 5`, and a graph homomorphism `G → C₅` is
  `Nonempty (G →g SimpleGraph.cycleGraph 5)`.
* The source asks a yes/no question without conjecturing an answer; `main` states the answer yes,
  and a disproof would answer no.
-/

namespace OMA.S_opg_pentagon_problem

/-- There exists `g` such that every finite 3-regular graph with no cycle of length shorter than
`g` admits a graph homomorphism to `C₅`. -/
theorem main : ∃ g : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsRegularOfDegree 3 →
    (∀ (v : V) (p : G.Walk v v), p.IsCycle → g ≤ p.length) →
    Nonempty (G →g SimpleGraph.cycleGraph 5) := by
  sorry

end OMA.S_opg_pentagon_problem
