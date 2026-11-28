import Mathlib

/-!
# Ringel–Kotzig conjecture (graceful tree conjecture)

Source: https://en.wikipedia.org/wiki/Ringel–Kotzig_conjecture
(redirects to https://en.wikipedia.org/wiki/Graceful_labeling)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Source statement: a graceful labeling of a graph with `m` edges is a labeling of its vertices
with some subset of the integers from `0` to `m` inclusive, such that no two vertices share a
label, and each edge is uniquely identified by the absolute difference between its endpoints,
such that this magnitude lies between `1` and `m` inclusive. The graceful tree conjecture, or
Ringel–Kotzig conjecture, hypothesizes that all trees are graceful.

Conventions:
* trees are finite simple graphs `G` on a finite vertex type `V` with Mathlib's
  `SimpleGraph.IsTree` (connected and acyclic; in particular `V` is non-empty);
* `m` is the number of edges, `G.edgeFinset.card`;
* a graceful labeling is `f : V → ℕ`, injective (no two vertices share a label), with every label
  at most `m`, such that the edge label `|f u - f v|` (computed in `ℤ`, then `Int.natAbs`) lies
  in `[1, m]` and determines the edge: two edges with the same label are the same edge (equality
  in `Sym2 V`). The bound `1 ≤ |f u - f v| ≤ m` is listed explicitly as in the source, although
  it already follows from injectivity and the label range.
-/

namespace OMA.S_wp_ringel_kotzig_conjecture

/-- `G` has a graceful labeling. -/
def IsGraceful {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ f : V → ℕ, Function.Injective f ∧ (∀ v, f v ≤ G.edgeFinset.card) ∧
    (∀ u v, G.Adj u v →
      1 ≤ Int.natAbs ((f u : ℤ) - f v) ∧ Int.natAbs ((f u : ℤ) - f v) ≤ G.edgeFinset.card) ∧
    (∀ u v u' v', G.Adj u v → G.Adj u' v' →
      Int.natAbs ((f u : ℤ) - f v) = Int.natAbs ((f u' : ℤ) - f v') → s(u, v) = s(u', v'))

theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsTree → IsGraceful G := by
  sorry

end OMA.S_wp_ringel_kotzig_conjecture
