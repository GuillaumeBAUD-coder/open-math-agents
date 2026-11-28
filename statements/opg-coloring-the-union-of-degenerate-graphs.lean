import Mathlib

/-!
# Coloring the union of degenerate graphs

Source: https://www.openproblemgarden.org/op/coloring_the_union_of_degenerate_graphs
Credit: @joshuadc11

Tarsi's conjecture: the union of a 1-degenerate graph (a forest) and a 2-degenerate graph is
5-colourable.

## Encoding

* Both graphs `G₁` and `G₂` are finite `SimpleGraph V` on a common finite vertex set `V` (without
  loss of generality, by adding isolated vertices to each graph on the union of their vertex sets),
  and their union is `G₁ ⊔ G₂`.
* A finite graph is `d`-degenerate iff every nonempty induced subgraph has a vertex of degree at
  most `d` (equivalently, it reduces to the empty graph by repeatedly deleting vertices of degree
  at most `d`).
* 5-colourable is Mathlib's `Nonempty ((G₁ ⊔ G₂).Coloring (Fin 5))`.
-/

namespace OMA.S_opg_coloring_the_union_of_degenerate_graphs

/-- `G` is `d`-degenerate: every nonempty finite induced subgraph has a vertex of degree at most
`d`. -/
def IsDegenerate {V : Type} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, (G.neighborSet v ∩ (S : Set V)).ncard ≤ d

/-- The union of a 1-degenerate graph and a 2-degenerate graph is 5-colourable. -/
theorem main : ∀ (V : Type) [Fintype V] (G₁ G₂ : SimpleGraph V),
    IsDegenerate G₁ 1 → IsDegenerate G₂ 2 →
    Nonempty ((G₁ ⊔ G₂).Coloring (Fin 5)) := by
  sorry

end OMA.S_opg_coloring_the_union_of_degenerate_graphs
