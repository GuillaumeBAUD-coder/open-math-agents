import Mathlib

/-!
# Splitting a digraph with minimum outdegree constraints

Source: https://www.openproblemgarden.org/op/splitting_a_digraph_with_minimum_outdegree_constraints
Credit: @shc261392

Problem (Alon): is there a minimum integer `f(d)` such that the vertices of any digraph with
minimum outdegree `f(d)` can be partitioned into two classes so that the minimum outdegree of
the subgraph induced by each class is at least `d`?

Reading used here:
* The question is whether such an `f(d)` exists for every `d` (then a least one exists); the
  statement is the affirmative answer, and a proof of its negation answers it in the negative.
* A digraph is a loopless relation `D : V → V → Prop` on a finite nonempty type `V`; the
  outdegree of `v` is the number of `w` with `D v w`, and a digraph with minimum outdegree at
  least `f(d)` is covered (the minimum outdegree `f(d)` of the source is a lower bound; adding
  arcs cannot hurt a digraph of larger minimum outdegree, which has a spanning subdigraph of
  minimum outdegree exactly `f(d)`).
* A partition into two classes is a set `A` with `A` and its complement both nonempty; in the
  subgraph induced by a class, the outdegree of `v` counts the `w` in the same class.
-/

namespace OMA.S_opg_splitting_a_digraph_with_minimum_outdegree_constraints

theorem main :
    ∀ d : ℕ, ∃ f : ℕ, ∀ (V : Type) [Fintype V] [Nonempty V] (D : V → V → Prop),
      (∀ v, ¬ D v v) → (∀ v, f ≤ {w | D v w}.ncard) →
        ∃ A : Set V, A.Nonempty ∧ Aᶜ.Nonempty ∧
          (∀ v ∈ A, d ≤ {w | w ∈ A ∧ D v w}.ncard) ∧
          (∀ v ∈ Aᶜ, d ≤ {w | w ∈ Aᶜ ∧ D v w}.ncard) := by
  sorry

end OMA.S_opg_splitting_a_digraph_with_minimum_outdegree_constraints
