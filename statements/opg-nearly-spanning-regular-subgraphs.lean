import Mathlib

/-!
# Nearly spanning regular subgraphs

Source: https://www.openproblemgarden.org/op/nearly_spanning_regular_subgraphs
Credit: @lzvxck

The source (Alon): for every `ε > 0` and every positive integer `k`, there exists
`r₀ = r₀(ε, k)` so that every simple `r`-regular graph `G` with `r ≥ r₀` has a `k`-regular
subgraph `H` with `|V(H)| ≥ (1 - ε) |V(G)|`.

Graphs are finite. A subgraph `H` of `G` is `k`-regular when every vertex of `H` has exactly
`k` neighbours in `H`.
-/

namespace OMA.S_opg_nearly_spanning_regular_subgraphs

/-- The subgraph `H` is `k`-regular: each of its vertices has exactly `k` neighbours in `H`. -/
def IsRegularSubgraph {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) (k : ℕ) : Prop :=
  ∀ v ∈ H.verts, (H.neighborSet v).ncard = k

/-- **Nearly spanning regular subgraphs.** For every `ε > 0` and `k ≥ 1` there is `r₀` such
that every finite simple `r`-regular graph with `r ≥ r₀` has a `k`-regular subgraph on at least
`(1 - ε) |V(G)|` vertices. -/
theorem main : ∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 0 < k → ∃ r₀ : ℕ,
    ∀ (r : ℕ), r₀ ≤ r → ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree r → ∃ H : G.Subgraph, IsRegularSubgraph H k ∧
        (1 - ε) * (Fintype.card V : ℝ) ≤ (H.verts.ncard : ℝ) := by
  sorry

end OMA.S_opg_nearly_spanning_regular_subgraphs
