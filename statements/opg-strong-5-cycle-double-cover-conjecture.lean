import Mathlib

/-!
# Strong 5-cycle double cover conjecture

Source: https://www.openproblemgarden.org/op/strong_5_cycle_double_cover_conjecture
Credit: @joshuadc11

Hoffmann-Ostenhof's Strong 5-Cycle Double Cover Conjecture: let `C` be a circuit (simple cycle) in
a finite bridgeless cubic graph `G`. Then `G` admits a 5-cycle double cover — five 2-regular
subgraphs (unions of vertex-disjoint circuits, possibly empty) covering every edge of `G` exactly
twice — such that `C` is a subgraph of one of these five 2-regular subgraphs.

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s; cubic is `G.IsRegularOfDegree 3`; bridgeless is
  `∀ e ∈ G.edgeSet, ¬ G.IsBridge e`.
* A circuit `C` in `G` is a walk `p : G.Walk v v` with `p.IsCycle`.
* A 2-regular subgraph (possibly empty, i.e., a disjoint union of circuits) is represented as a
  spanning subgraph `H ≤ G` in which every vertex has degree `0` or `2`.
* Covering every edge of `G` exactly twice is
  `∀ e ∈ G.edgeSet, {i : Fin 5 | e ∈ (H i).edgeSet}.ncard = 2`.
* `C` being a subgraph of `H i` is `∀ e ∈ p.edges, e ∈ (H i).edgeSet`.
-/

namespace OMA.S_opg_strong_5_cycle_double_cover_conjecture

/-- Every finite bridgeless cubic graph `G` with a distinguished circuit `p` admits five 2-regular
subgraphs covering every edge of `G` twice, one of which contains `p`. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsRegularOfDegree 3 →
    (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) →
    ∀ (v : V) (p : G.Walk v v), p.IsCycle →
      ∃ H : Fin 5 → SimpleGraph V,
        (∀ i, H i ≤ G) ∧
        (∀ i (u : V), ((H i).neighborSet u).ncard = 0 ∨ ((H i).neighborSet u).ncard = 2) ∧
        (∀ e ∈ G.edgeSet, {i : Fin 5 | e ∈ (H i).edgeSet}.ncard = 2) ∧
        (∃ i : Fin 5, ∀ e ∈ p.edges, e ∈ (H i).edgeSet) := by
  sorry

end OMA.S_opg_strong_5_cycle_double_cover_conjecture
