import Mathlib

/-!
# Friendly partitions

Source: https://www.openproblemgarden.org/op/friendly_partitions
Credit: @ishaanzee

A friendly partition of a graph is a partition of the vertices into two sets so that every
vertex has at least as many neighbours in its own class as in the other.

**Problem** (M. DeVos). Is it true that for every `r`, all but finitely many `r`-regular graphs
have friendly partitions?

Formalization choices (we state the affirmative answer):
* Graphs are finite simple graphs.
* A partition into two sets has two nonempty classes `A` and `Aᶜ`. (Allowing an empty class
  would make every graph trivially friendly; the source's remark that for `r = 3` the problem
  reduces to finding two vertex-disjoint cycles uses nonempty classes.)
* "All but finitely many `r`-regular graphs" (up to isomorphism) is equivalent to "every
  `r`-regular graph with at least `N` vertices, for some `N`": there are only finitely many
  graphs on fewer than `N` vertices up to isomorphism, and a finite set of exceptions has
  bounded size.
-/

namespace OMA.S_opg_friendly_partitions

/-- `A` and its complement form a friendly partition of `G`: both classes are nonempty and every
vertex has at least as many neighbours in its own class as in the other class. -/
def IsFriendlyPartition {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) : Prop :=
  A.Nonempty ∧ Aᶜ.Nonempty ∧ ∀ v : V,
    ((G.neighborFinset v).filter fun w => ¬ (w ∈ A ↔ v ∈ A)).card ≤
      ((G.neighborFinset v).filter fun w => (w ∈ A ↔ v ∈ A)).card

/-- **DeVos' question**, affirmative form: for every `r` there is `N` such that every `r`-regular
graph on at least `N` vertices has a friendly partition. -/
theorem main : ∀ r : ℕ, ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], G.IsRegularOfDegree r → N ≤ Fintype.card V →
      ∃ A : Finset V, IsFriendlyPartition G A := by
  sorry

end OMA.S_opg_friendly_partitions
