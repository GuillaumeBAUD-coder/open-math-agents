import Mathlib

/-!
# Black and White Cycle Conjecture

Source: https://www.openproblemgarden.org/op/black_and_white_cycle_conjecture
Credit: @shc261392

Conjecture: let `G` be a cubic graph with a nowhere-zero 4-flow. Colour an edge `e` black if
`G - e` has no nowhere-zero 4-flow, and white if `G - e` has one. Then `G` contains a white
cycle but no black cycle (a cycle is a connected 2-regular subgraph; it is black, resp. white,
if all its edges are black, resp. white).

Reading used here:
* `G` is a finite simple cubic graph on a nonempty vertex type.
* By Tutte's theorem the existence of a nowhere-zero `A`-flow depends only on `|A|`, so a
  nowhere-zero 4-flow on an edge set `F` is taken with values in the Klein group
  `ZMod 2 × ZMod 2`, where orientations play no role: a map `f` that is nonzero on every edge
  of `F` and whose values on the edges of `F` at each vertex sum to zero.
* `G - e` is the spanning subgraph with edge set `G.edgeSet \ {e}`.
* A cycle is a closed walk `p` with `p.IsCycle`; its edges are `p.edges`.
-/

namespace OMA.S_opg_black_and_white_cycle_conjecture

/-- The spanning subgraph with edge set `F` has a nowhere-zero 4-flow (Klein group values). -/
def HasNZ4Flow {V : Type} (F : Set (Sym2 V)) : Prop :=
  ∃ f : Sym2 V → ZMod 2 × ZMod 2, (∀ e ∈ F, f e ≠ 0) ∧
    ∀ v : V, ∑ᶠ w ∈ {w : V | s(v, w) ∈ F}, f s(v, w) = 0

/-- `e` is black: `G - e` has no nowhere-zero 4-flow. -/
def IsBlack {V : Type} (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  ¬ HasNZ4Flow (G.edgeSet \ {e})

theorem main :
    ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree 3 → HasNZ4Flow G.edgeSet →
        (∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ ∀ e ∈ p.edges, ¬ IsBlack G e) ∧
        ¬ ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ ∀ e ∈ p.edges, IsBlack G e := by
  sorry

end OMA.S_opg_black_and_white_cycle_conjecture
