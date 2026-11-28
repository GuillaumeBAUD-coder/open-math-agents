import Mathlib

/-!
# Degenerate colorings of planar graphs

Source: https://www.openproblemgarden.org/op/degenerate_colorings_of_planar_graphs
Credit: @joshuadc11

Borodin's conjecture: every simple planar graph has a 5-coloring such that for every `1 ≤ k ≤ 4`,
the union of any `k` color classes induces a `(k - 1)`-degenerate graph.

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s.
* Planarity is the plane-drawing definition used in `statements/wp-apex-graph.lean` and
  `statements/opg-circular-chromatic-number-of-triangle-free-planar-graphs.lean`.
* A graph is `d`-degenerate if every nonempty finite induced subgraph (equivalently, every nonempty
  subgraph) has a vertex of degree at most `d`.
* A proper 5-coloring is `c : G.Coloring (Fin 5)`. For any subset `C : Finset (Fin 5)` with
  `1 ≤ C.card ≤ 4`, the induced subgraph on `{v : V | c v ∈ C}` is `(C.card - 1)`-degenerate.
-/

namespace OMA.S_opg_degenerate_colorings_of_planar_graphs

/-- `G` has a plane drawing: vertices at distinct points, edges as arcs joining their endpoints,
with arc interiors avoiding all vertices and the interiors of all other arcs. -/
def IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (pos : V → ℝ × ℝ) (arc : G.edgeSet → C(unitInterval, ℝ × ℝ)),
    Function.Injective pos ∧
    (∀ e, Function.Injective (arc e)) ∧
    (∀ e, Sym2.map pos e.1 = s(arc e 0, arc e 1)) ∧
    (∀ e (t : unitInterval), (t : ℝ) ∈ Set.Ioo 0 1 → ∀ v, arc e t ≠ pos v) ∧
    (∀ e f, e ≠ f → ∀ s t : unitInterval, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      arc e s ≠ arc f t)

/-- `G` is `d`-degenerate: every nonempty finite induced subgraph has a vertex of degree at most
`d`. -/
def IsDegenerate {V : Type} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, (G.neighborSet v ∩ (S : Set V)).ncard ≤ d

/-- Every finite simple planar graph has a proper 5-coloring such that for every `1 ≤ k ≤ 4`, the
union of any `k` color classes induces a `(k - 1)`-degenerate graph. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsPlanar G →
    ∃ c : G.Coloring (Fin 5), ∀ C : Finset (Fin 5), 1 ≤ C.card → C.card ≤ 4 →
      IsDegenerate (G.induce {v : V | c v ∈ C}) (C.card - 1) := by
  sorry

end OMA.S_opg_degenerate_colorings_of_planar_graphs
