import Mathlib

/-!
# 5-flow conjecture

Source: https://www.openproblemgarden.org/op/5_flow_conjecture
Credit: @lzvxck

Tutte's 5-flow conjecture: every bridgeless graph has a nowhere-zero 5-flow.

A nowhere-zero `k`-flow assigns to each edge an orientation and a value in
`{±1, …, ±(k-1)}` so that at every vertex the inflow equals the outflow. Here it is encoded,
without choosing an orientation, as an antisymmetric function `φ u v = - φ v u` on ordered
pairs of adjacent vertices with `0 < |φ u v| < k`, vanishing on non-adjacent pairs, whose net
outflow `∑ v, φ u v` is zero at every vertex `u`.

The statement is for finite simple graphs. This is equivalent to the multigraph version:
subdividing every edge (loops and parallel edges included) yields a simple graph, and both
bridgelessness and nowhere-zero `k`-flows are preserved in both directions by subdivision.
-/

namespace OMA.S_opg_5_flow_conjecture

/-- `φ` is a nowhere-zero `k`-flow on `G` (an integer flow, encoded on ordered pairs). -/
def IsNowhereZeroFlow {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) (φ : V → V → ℤ) :
    Prop :=
  (∀ u v, φ u v = - φ v u) ∧
  (∀ u v, ¬ G.Adj u v → φ u v = 0) ∧
  (∀ u v, G.Adj u v → 0 < |φ u v| ∧ |φ u v| < k) ∧
  (∀ u, ∑ v, φ u v = 0)

/-- **Tutte's 5-flow conjecture.** Every finite bridgeless graph has a nowhere-zero 5-flow. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) → ∃ φ : V → V → ℤ, IsNowhereZeroFlow G 5 φ := by
  sorry

end OMA.S_opg_5_flow_conjecture
