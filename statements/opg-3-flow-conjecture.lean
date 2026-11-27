import Mathlib

/-!
# 3-flow conjecture

Source: https://www.openproblemgarden.org/op/3_flow_conjecture
Credit: @John-A-McMahon

Source statement (Open Problem Garden, Tutte): every 4-edge-connected graph has a nowhere-zero
3-flow.

Graphs are finite and may have parallel edges and loops (the source states no restriction; the
conjecture is about finite multigraphs). A graph is given by a finite vertex type `V`, a finite
edge type `E` and endpoint maps `src tgt : E → V`, which also fix a reference orientation;
whether a nowhere-zero `k`-flow exists does not depend on the orientation chosen. The graph is
4-edge-connected if deleting any set of fewer than 4 edges leaves every two vertices connected.
A nowhere-zero `k`-flow is an integer flow `φ : E → ℤ` with `0 < |φ e| < k` on every edge,
conserved at every vertex (inflow = outflow; a loop at `v` contributes equally to both sides).
-/

namespace OMA.S_opg_3_flow_conjecture

open Finset

variable {V E : Type}

/-- Two vertices are joined by an edge outside `F`. -/
def AdjAvoiding (src tgt : E → V) (F : Finset E) (x y : V) : Prop :=
  ∃ f : E, f ∉ F ∧ ((src f = x ∧ tgt f = y) ∨ (src f = y ∧ tgt f = x))

/-- `k`-edge-connected: deleting fewer than `k` edges leaves all vertices connected. -/
def IsKEdgeConnected (src tgt : E → V) (k : ℕ) : Prop :=
  ∀ F : Finset E, F.card < k → ∀ x y : V, Relation.ReflTransGen (AdjAvoiding src tgt F) x y

/-- A nowhere-zero integer `k`-flow with respect to the orientation `src → tgt`. -/
def IsNowhereZeroFlow [Fintype E] [DecidableEq V] (src tgt : E → V) (k : ℕ) (φ : E → ℤ) :
    Prop :=
  (∀ e, φ e ≠ 0 ∧ |φ e| < k) ∧
    ∀ v : V, ∑ e ∈ univ.filter (fun e => tgt e = v), φ e =
      ∑ e ∈ univ.filter (fun e => src e = v), φ e

theorem main :
    ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] (src tgt : E → V),
      IsKEdgeConnected src tgt 4 → ∃ φ : E → ℤ, IsNowhereZeroFlow src tgt 3 φ := by
  sorry

end OMA.S_opg_3_flow_conjecture
