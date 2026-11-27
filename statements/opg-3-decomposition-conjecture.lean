import Mathlib

/-!
# 3-Decomposition Conjecture

Source: https://www.openproblemgarden.org/op/3_decomposition_conjecture
Credit: @joshuadc11

Hoffmann-Ostenhof's 3-Decomposition Conjecture: every finite connected cubic graph `G` has an
edge-decomposition into a spanning tree `H₁`, a nonempty 2-regular subgraph `H₂` (a nonempty
union of vertex-disjoint cycles), and a possibly empty matching `H₃`.

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s; cubic means `G.IsRegularOfDegree 3`.
* `H₁`, `H₂`, `H₃` are represented as `SimpleGraph V` on the same vertex set `V` whose edge sets
  are pairwise disjoint and have union `G.edgeSet`.
* `H₁.IsTree` asserts that `H₁` is a spanning tree of `G`. Note that since `G` is connected and
  3-regular, `V` has at least 4 vertices, so `H₁` is automatically nonempty.
* `H₂.edgeSet.Nonempty ∧ ∀ v : V, (H₂.neighborSet v).ncard = 0 ∨ (H₂.neighborSet v).ncard = 2`
  asserts that `H₂` is a nonempty 2-regular subgraph of `G` (a nonempty family of vertex-disjoint
  cycles, ignoring isolated vertices outside `V(H₂)`).
* `∀ v : V, (H₃.neighborSet v).ncard ≤ 1` asserts that `H₃` is a (possibly empty) matching.
-/

namespace OMA.S_opg_3_decomposition_conjecture

/-- Every finite connected cubic graph decomposes into a spanning tree `H₁`, a nonempty 2-regular
subgraph `H₂`, and a possibly empty matching `H₃`. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → G.IsRegularOfDegree 3 →
    ∃ H₁ H₂ H₃ : SimpleGraph V,
      H₁.IsTree ∧
      H₂.edgeSet.Nonempty ∧
      (∀ v : V, (H₂.neighborSet v).ncard = 0 ∨ (H₂.neighborSet v).ncard = 2) ∧
      (∀ v : V, (H₃.neighborSet v).ncard ≤ 1) ∧
      H₁.edgeSet ∪ H₂.edgeSet ∪ H₃.edgeSet = G.edgeSet ∧
      Disjoint H₁.edgeSet H₂.edgeSet ∧
      Disjoint H₁.edgeSet H₃.edgeSet ∧
      Disjoint H₂.edgeSet H₃.edgeSet := by
  sorry

end OMA.S_opg_3_decomposition_conjecture
