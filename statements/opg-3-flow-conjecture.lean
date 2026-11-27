import Mathlib

/-!
# 3-flow conjecture

Source: https://www.openproblemgarden.org/op/3_flow_conjecture
Credit: @lzvxck

Tutte's 3-flow conjecture, as stated in the source: every 4-edge-connected graph has a
nowhere-zero 3-flow.

Graphs in flow theory may have parallel edges and loops, and edge-connectivity is sensitive to
parallel edges, so the statement is made for finite multigraphs: a finite vertex type `V`, a
finite edge type `E`, and for each edge `e` a tail `src e` and a head `tgt e` (a reference
orientation; reversing an edge negates its flow value, so the choice is immaterial).

* A nowhere-zero `k`-flow is `f : E → ℤ` with `0 < |f e| < k` for every edge and, at every
  vertex, total inflow equal to total outflow.
* The multigraph is `k`-edge-connected if it stays connected after deleting any set of fewer
  than `k` edges.
-/

namespace OMA.S_opg_3_flow_conjecture

/-- The simple graph recording which distinct vertices are joined by an edge outside `S`;
it is connected exactly when the multigraph minus the edges `S` is connected. -/
def underlying {V E : Type*} (src tgt : E → V) (S : Set E) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => ∃ e, e ∉ S ∧ src e = u ∧ tgt e = v

/-- The multigraph `(V, E, src, tgt)` is `k`-edge-connected: deleting any set of fewer than `k`
edges leaves it connected. -/
def IsEdgeConnected {V E : Type*} [Fintype E] (src tgt : E → V) (k : ℕ) : Prop :=
  ∀ S : Finset E, S.card < k → (underlying src tgt (S : Set E)).Connected

/-- `f` is a nowhere-zero `k`-flow on the multigraph `(V, E, src, tgt)`. -/
def IsNowhereZeroFlow {V E : Type*} [Fintype E] [DecidableEq V] (src tgt : E → V) (k : ℕ)
    (f : E → ℤ) : Prop :=
  (∀ e, 0 < |f e| ∧ |f e| < k) ∧
  ∀ v, ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), f e =
    ∑ e ∈ Finset.univ.filter (fun e => src e = v), f e

/-- **Tutte's 3-flow conjecture.** Every finite 4-edge-connected multigraph has a nowhere-zero
3-flow. -/
theorem main : ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] (src tgt : E → V),
    IsEdgeConnected src tgt 4 → ∃ f : E → ℤ, IsNowhereZeroFlow src tgt 3 f := by
  sorry

end OMA.S_opg_3_flow_conjecture
