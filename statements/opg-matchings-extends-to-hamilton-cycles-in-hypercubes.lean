import Mathlib

/-!
# Matchings extend to Hamiltonian cycles in hypercubes

Source: https://www.openproblemgarden.org/op/matchings_extends_to_hamilton_cycles_in_hypercubes
(F. Ruskey and C. Savage, question 3 on page 19 of *Matchings extend to Hamiltonian cycles in
hypercubes*)
Credit: @ishaanzee

**Question.** Does every matching of the hypercube `Q_d` extend to a Hamiltonian cycle?

The answer is positive for `d ≤ 4`, and Fink proved Kreweras' conjecture that every *perfect*
matching of `Q_d` extends to a Hamiltonian cycle. We state the affirmative answer.

Formalization:
* `Q_d` has vertex set `Fin d → Bool`, two words being adjacent when they differ in exactly one
  coordinate. We take `d ≥ 2`: `Q_0` and `Q_1` have no cycles at all, so the question concerns
  `d ≥ 2`.
* A matching of `Q_d` is a subgraph `M` with `M.IsMatching` (Mathlib: every vertex of `M` has
  exactly one neighbour in `M`), i.e. a set of pairwise disjoint edges.
* `M` extends to a Hamiltonian cycle if some Hamiltonian cycle `c` of `Q_d`
  (`SimpleGraph.Walk.IsHamiltonianCycle`) uses every edge of `M`.
-/

namespace OMA.S_opg_matchings_extends_to_hamilton_cycles_in_hypercubes

/-- The `d`-dimensional hypercube graph `Q_d`: binary words of length `d`, adjacent when they
differ in exactly one coordinate. -/
def cube (d : ℕ) : SimpleGraph (Fin d → Bool) :=
  SimpleGraph.fromRel fun x y => (Finset.univ.filter fun i => x i ≠ y i).card = 1

/-- **Ruskey–Savage question**, affirmative form: for `d ≥ 2`, every matching of `Q_d` is
contained in (the edge set of) some Hamiltonian cycle of `Q_d`. -/
theorem main : ∀ d : ℕ, 2 ≤ d → ∀ M : (cube d).Subgraph, M.IsMatching →
    ∃ (v : Fin d → Bool) (c : (cube d).Walk v v), c.IsHamiltonianCycle ∧
      ∀ e ∈ M.edgeSet, e ∈ c.edges := by
  sorry

end OMA.S_opg_matchings_extends_to_hamilton_cycles_in_hypercubes
