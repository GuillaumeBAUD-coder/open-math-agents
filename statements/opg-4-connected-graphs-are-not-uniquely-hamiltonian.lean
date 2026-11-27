import Mathlib

/-!
# 4-connected graphs are not uniquely hamiltonian

Source: https://www.openproblemgarden.org/op/4_connected_graphs_are_not_uniquely_hamiltonian
Credit: @lzvxck

The source: every 4-connected graph with a Hamilton cycle has a second Hamilton cycle.

Conventions: graphs are finite and simple. `G` is `k`-connected if it has more than `k`
vertices and stays connected after deleting any set of fewer than `k` vertices. A Hamilton
cycle is a cycle through every vertex; two Hamilton cycles are different when their edge sets
differ (so a cycle, its reversal and its rotations count as the same cycle).
-/

namespace OMA.S_opg_4_connected_graphs_are_not_uniquely_hamiltonian

/-- `G` is `k`-connected: more than `k` vertices, and deleting fewer than `k` vertices leaves
a connected graph. -/
def IsKConnected {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Connected

/-- `c` is a Hamilton cycle of `G`: a cycle visiting every vertex. -/
def IsHamiltonCycle {V : Type*} (G : SimpleGraph V) {v : V} (c : G.Walk v v) : Prop :=
  c.IsCycle ∧ ∀ w, w ∈ c.support

/-- **4-connected graphs are not uniquely hamiltonian.** Every 4-connected graph with a
Hamilton cycle has a second Hamilton cycle (with a different edge set). -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsKConnected G 4 → ∀ (v : V) (c : G.Walk v v), IsHamiltonCycle G c →
      ∃ (w : V) (d : G.Walk w w), IsHamiltonCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset := by
  sorry

end OMA.S_opg_4_connected_graphs_are_not_uniquely_hamiltonian
