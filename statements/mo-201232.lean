import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Image

namespace OMA.S_mo_201232

/-- A pure graph has a nonempty set of two-element edges and no isolated vertices. -/
def PureGraph {n : ℕ} (edges : Finset (Finset (Fin n))) : Prop :=
  edges.Nonempty ∧
    (∀ e ∈ edges, e.card = 2) ∧
    ∀ v : Fin n, ∃ e ∈ edges, v ∈ e

/-- The face poset of the graph, with the empty face as the bottom element. -/
def faces {n : ℕ} (edges : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  insert ∅ (Finset.univ.image (fun v : Fin n => ({v} : Finset (Fin n))) ∪ edges)

abbrev Face {n : ℕ} (edges : Finset (Finset (Fin n))) := ↥(faces edges)

/-- For graphs, lifting a maximal chain means lifting its vertex-edge incidence.
Pure graph face posets are a subclass of the CW posets in the question. -/
theorem main :
    ∀ (p q : ℕ) (P : Finset (Finset (Fin p))) (Q : Finset (Finset (Fin q))),
      PureGraph P → PureGraph Q →
        ∀ f : Face P → Face Q, Function.Surjective f →
          (∀ x y : Face P, x.val ⊆ y.val → (f x).val ⊆ (f y).val) →
          (∀ x : Face P, (f x).val.card = x.val.card) →
            ∀ v e : Face Q, v.val.card = 1 → e.val.card = 2 → v.val ⊆ e.val →
              ∃ x y : Face P, x.val ⊆ y.val ∧ f x = v ∧ f y = e := by
  sorry

end OMA.S_mo_201232
