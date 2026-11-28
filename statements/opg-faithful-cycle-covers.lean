import Mathlib

/-!
# Faithful cycle covers

Source: https://www.openproblemgarden.org/op/faithful_cycle_covers
(P. D. Seymour, *Sums of circuits*, in Graph Theory and Related Topics, Academic Press 1979, 341–355.)
Credit: @k-okubo (agent: Claude Code, model claude-opus-5-5)

**Conjecture (Seymour).** Let `G = (V, E)` be a graph and `p : E → ℤ` be admissible. If `p(e)` is even
for every `e ∈ E(G)`, then `(G, p)` has a faithful cover.

Definitions, as on the source page:
* `p` is *admissible* if (i) `p` is nonnegative, (ii) `p(S)` is even for every edge-cut `S`, and
  (iii) `p(e) ≤ p(S) / 2` for every edge-cut `S` and every `e ∈ S`. Here `p(S) = ∑_{e ∈ S} p(e)`.
* A list `L` of cycles of `G` is a *faithful (cycle) cover* of `(G, p)` if every edge `e` of `G` occurs
  in exactly `p(e)` cycles of `L` (a list: the same cycle may occur several times).

Conventions of this formalization:
* `G` is a finite simple graph. The source does not exclude parallel edges or loops, but nothing is
  lost: a loop lies in no edge-cut and, having even weight, is covered by that many copies of itself;
  subdividing a parallel edge into a path of two edges of the same weight preserves admissibility
  and faithful covers in both directions. So the statement for finite simple graphs is equivalent.
* An edge-cut is the set `δ(X)` of edges with exactly one end in `X`, for a set `X` of vertices
  (the empty cut is harmless: it satisfies (ii) and (iii) trivially).
* A cycle is identified with its edge set, the edges of some `Walk.IsCycle`.
* `p` is a function `Sym2 V → ℤ`; only its values on edges of `G` matter.
-/

namespace OMA.S_opg_faithful_cycle_covers

open Classical

variable {V : Type*}

/-- The edge-cut `δ(X)`: the edges of `G` with exactly one end in `X`. -/
noncomputable def cut [Fintype V] (G : SimpleGraph V) (X : Set V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∃ u v, e = s(u, v) ∧ u ∈ X ∧ v ∉ X

/-- `p` is admissible: nonnegative on edges, even on every edge-cut, and no edge of a cut carries
more than half of the cut's weight. -/
def Admissible [Fintype V] (G : SimpleGraph V) (p : Sym2 V → ℤ) : Prop :=
  (∀ e ∈ G.edgeSet, 0 ≤ p e) ∧
  (∀ X : Set V, Even (∑ e ∈ cut G X, p e)) ∧
  (∀ X : Set V, ∀ e ∈ cut G X, 2 * p e ≤ ∑ f ∈ cut G X, p f)

/-- `C` is (the edge set of) a cycle of `G`. -/
def IsCycleEdgeSet (G : SimpleGraph V) (C : Finset (Sym2 V)) : Prop :=
  ∃ (u : V) (w : G.Walk u u), w.IsCycle ∧ C = w.edges.toFinset

/-- `L` is a faithful cover of `(G, p)`: a list of cycles of `G` in which every edge `e` of `G`
occurs in exactly `p e` cycles. -/
def IsFaithfulCover (G : SimpleGraph V) (p : Sym2 V → ℤ) (L : List (Finset (Sym2 V))) : Prop :=
  (∀ C ∈ L, IsCycleEdgeSet G C) ∧
  ∀ e ∈ G.edgeSet, ((L.filter fun C => e ∈ C).length : ℤ) = p e

/-- **Seymour's faithful cycle cover conjecture.** -/
theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (p : Sym2 V → ℤ),
      Admissible G p → (∀ e ∈ G.edgeSet, Even (p e)) →
        ∃ L : List (Finset (Sym2 V)), IsFaithfulCover G p L := by
  sorry

end OMA.S_opg_faithful_cycle_covers
