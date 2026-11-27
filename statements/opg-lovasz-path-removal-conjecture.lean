import Mathlib

/-!
# Lovász Path Removal Conjecture

Source: https://www.openproblemgarden.org/op/lovasz_path_removal_conjecture
Credit: @ishaanzee

**Conjecture** (L. Lovász). There is an integer-valued function `f(k)` such that if `G` is any
`f(k)`-connected graph and `x` and `y` are any two vertices of `G`, then there exists an induced
path `P` with ends `x` and `y` such that `G - V(P)` is `k`-connected.

(Tutte's theorem gives `f(1) = 3`; `f(2) = 5` by Chen–Gould–Yu and Kriesell.)

Formalization:
* Graphs are finite simple graphs. `k`-connected (vertex connectivity): more than `k` vertices,
  and connected after deleting any fewer than `k` vertices.
* `x` and `y` are two distinct vertices; a path from `x` to `y` is a `Walk` that `IsPath`. It is
  induced when every edge of `G` between two of its vertices is an edge of the path.
* `G - V(P)` is the subgraph of `G` induced on the vertices not on `P`.
-/

namespace OMA.S_opg_lovasz_path_removal_conjecture

/-- `G` is `k`-connected: it has more than `k` vertices and stays connected after deleting any
fewer than `k` vertices. -/
def IsKConnected {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Nat.card V ∧ ∀ S : Set V, S.Finite → S.ncard < k → (G.induce Sᶜ).Connected

/-- **Lovász' path removal conjecture.** -/
theorem main : ∃ f : ℕ → ℕ, ∀ (k : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsKConnected G (f k) → ∀ x y : V, x ≠ y →
      ∃ p : G.Walk x y, p.IsPath ∧
        (∀ u ∈ p.support, ∀ w ∈ p.support, G.Adj u w → s(u, w) ∈ p.edges) ∧
        IsKConnected (G.induce {v | v ∉ p.support}) k := by
  sorry

end OMA.S_opg_lovasz_path_removal_conjecture
