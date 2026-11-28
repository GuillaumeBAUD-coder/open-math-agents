import Mathlib

/-!
# Acyclic edge-colouring

Source: https://www.openproblemgarden.org/op/acyclic_edge_coloring
Credit: @joshuadc11

Fiamčík's acyclic edge-colouring conjecture: every finite simple graph `G` with maximum degree `Δ`
admits a proper `(Δ + 2)`-edge-colouring such that every cycle in `G` contains edges of at least
three distinct colours.

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s with maximum degree `G.maxDegree`.
* An edge-colouring with `G.maxDegree + 2` colours is a map `c : Sym2 V → Fin (G.maxDegree + 2)`.
* Properness: any two distinct edges incident to a common vertex `u` receive distinct colours,
  i.e., `G.Adj u v → G.Adj u w → v ≠ w → c s(u, v) ≠ c s(u, w)`.
* Acyclicity: for every cycle `p : G.Walk v v` with `p.IsCycle`, the set of colours
  `p.edges.toFinset.image c` has cardinality at least `3`.
-/

namespace OMA.S_opg_acyclic_edge_coloring

/-- Every finite simple graph `G` admits a proper `(G.maxDegree + 2)`-edge-colouring in which
every cycle uses at least three distinct colours. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ∃ c : Sym2 V → Fin (G.maxDegree + 2),
      (∀ u v w : V, G.Adj u v → G.Adj u w → v ≠ w → c s(u, v) ≠ c s(u, w)) ∧
      (∀ (v : V) (p : G.Walk v v), p.IsCycle → 3 ≤ (p.edges.toFinset.image c).card) := by
  sorry

end OMA.S_opg_acyclic_edge_coloring
