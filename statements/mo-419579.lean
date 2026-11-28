import Mathlib

namespace OMA.S_mo_419579

open scoped BigOperators

/-- A deletion order is valid when every nonempty remaining induced graph is connected. -/
def ValidDeletionOrder {V : Type*} [DecidableEq V] (G : SimpleGraph V) :
    List V → Prop
  | [] => True
  | v :: vs => (G.induce (↑(v :: vs).toFinset : Set V)).Connected ∧
      ValidDeletionOrder G vs

/-- All valid orders of deleting exactly the vertices of a set. -/
noncomputable def deletionOrders {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (s : Finset V) : Finset (List V) := by
  classical
  exact s.toList.permutations.toFinset.filter (ValidDeletionOrder G)

/-- One row of the subset dynamic program, using the values for smaller sets. -/
noncomputable def deletionStep {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (f : Finset V → ℕ) (s : Finset V) : ℕ := by
  classical
  exact if s = ∅ then 1 else if (G.induce (↑s : Set V)).Connected then
    ∑ v ∈ s, f (s.erase v)
  else 0

/-- For a finite graph, the full count is the value at `Finset.univ`.
The recurrence determines the count on all subsets, and the count on any
subset with at least two vertices is even. -/
theorem main :
    ∀ (V : Type) [DecidableEq V] (G : SimpleGraph V),
      (∀ f : Finset V → ℕ,
        (∀ s, f s = deletionStep G f s) ↔ f = fun s => (deletionOrders G s).card) ∧
      ∀ s : Finset V, 2 ≤ s.card → Even (deletionOrders G s).card := by
  sorry

end OMA.S_mo_419579
