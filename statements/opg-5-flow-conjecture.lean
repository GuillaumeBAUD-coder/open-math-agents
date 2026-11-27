import Mathlib

/-!
# 5-flow conjecture

Source: https://www.openproblemgarden.org/op/5_flow_conjecture
Credit: @John-A-McMahon

Source statement (Open Problem Garden, Tutte): every bridgeless graph has a nowhere-zero 5-flow.

Graphs are finite and may have parallel edges and loops (the source does not exclude them, and
Tutte's conjecture is about finite multigraphs). A graph is given by a finite vertex type `V`,
a finite edge type `E` and endpoint maps `src tgt : E → V`, which also fix a reference
orientation; whether a nowhere-zero `k`-flow exists does not depend on the orientation chosen.
An edge is a bridge if its two endpoints are no longer connected once it is removed (a loop is
never a bridge). A nowhere-zero `k`-flow is an integer flow `φ : E → ℤ` with
`0 < |φ e| < k` on every edge, conserved at every vertex (inflow = outflow; a loop at `v`
contributes equally to both sides).
-/

namespace OMA.S_opg_5_flow_conjecture

open Finset

variable {V E : Type}

/-- Two vertices are joined by an edge other than `e`. -/
def AdjWithout (src tgt : E → V) (e : E) (x y : V) : Prop :=
  ∃ f : E, f ≠ e ∧ ((src f = x ∧ tgt f = y) ∨ (src f = y ∧ tgt f = x))

/-- `e` is a bridge: after deleting `e`, its endpoints are not connected. -/
def IsBridge (src tgt : E → V) (e : E) : Prop :=
  ¬ Relation.ReflTransGen (AdjWithout src tgt e) (src e) (tgt e)

/-- A nowhere-zero integer `k`-flow with respect to the orientation `src → tgt`. -/
def IsNowhereZeroFlow [Fintype E] [DecidableEq V] (src tgt : E → V) (k : ℕ) (φ : E → ℤ) :
    Prop :=
  (∀ e, φ e ≠ 0 ∧ |φ e| < k) ∧
    ∀ v : V, ∑ e ∈ univ.filter (fun e => tgt e = v), φ e =
      ∑ e ∈ univ.filter (fun e => src e = v), φ e

theorem main :
    ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] (src tgt : E → V),
      (∀ e, ¬ IsBridge src tgt e) → ∃ φ : E → ℤ, IsNowhereZeroFlow src tgt 5 φ := by
  sorry

end OMA.S_opg_5_flow_conjecture
