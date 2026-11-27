import Mathlib

/-!
# Splitting a digraph with minimum outdegree constraints

Source: https://www.openproblemgarden.org/op/splitting_a_digraph_with_minimum_outdegree_constraints
Credit: @ishaanzee

**Problem** (N. Alon). Is there a minimum integer `f(d)` such that the vertices of any digraph with
minimum outdegree `f(d)` can be partitioned into two classes so that the minimum outdegree of the
subgraph induced by each class is at least `d`?

(Thomassen proved `f(1) = 3`.) We state the affirmative answer: such an `f(d)` exists for every
`d`.

Formalization:
* A digraph on a finite nonempty vertex set `V` is a relation `D : V → V → Prop` without loops
  (`D v w` is the arc `v → w`; no parallel arcs, 2-cycles allowed).
* Minimum outdegree at least `m`: every vertex has at least `m` out-neighbours.
* The two classes `A` and `Aᶜ` are nonempty (otherwise the whole digraph would trivially be one
  class), and every vertex has at least `d` out-neighbours inside its own class.
-/

namespace OMA.S_opg_splitting_a_digraph_with_minimum_outdegree_constraints

/-- **Alon's problem**, affirmative form: for every `d` there is `f` such that every finite digraph
of minimum outdegree at least `f` splits into two nonempty classes, each inducing a digraph of
minimum outdegree at least `d`. -/
theorem main : ∀ d : ℕ, ∃ f : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (D : V → V → Prop) [DecidableRel D], (∀ v, ¬ D v v) →
    (∀ v, f ≤ (Finset.univ.filter fun w => D v w).card) →
      ∃ A : Finset V, A.Nonempty ∧ Aᶜ.Nonempty ∧
        (∀ v ∈ A, d ≤ (A.filter fun w => D v w).card) ∧
        (∀ v ∈ Aᶜ, d ≤ (Aᶜ.filter fun w => D v w).card) := by
  sorry

end OMA.S_opg_splitting_a_digraph_with_minimum_outdegree_constraints
