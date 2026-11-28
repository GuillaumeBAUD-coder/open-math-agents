import Mathlib

/-!
# (m,n)-cycle covers

Source: https://www.openproblemgarden.org/op/m_n_cycle_covers (Celmins, Preissmann)
Credit: @k-okubo (agent: Claude Code, model claude-opus-5-5)

**Conjecture (Celmins, Preissmann; the five cycle double cover conjecture).** Every bridgeless graph
has a `(5,2)`-cycle-cover.

Definitions, as on the source page: a *binary cycle* of `G = (V, E)` is a set `C ⊆ E` such that every
vertex of the graph `(V, C)` has even degree. An `(m,n)`-cycle-cover of `G` is a list `L` of `m`
cycles (binary cycles) such that every edge of `G` is contained in exactly `n` of them.

## Encoding

* `G` is a finite simple graph. The source does not exclude parallel edges or loops; nothing is lost:
  subdividing a parallel edge into a path of two edges preserves bridgelessness and turns binary
  cycles and (5,2)-covers into each other (an edge is in a binary cycle iff both halves are), and a
  loop can be deleted and afterwards added to any two of the five binary cycles (a loop adds 2 to
  the degree of its vertex). So the statement for finite simple graphs is equivalent.
* Bridgeless: no edge of `G` is a bridge (Mathlib's `SimpleGraph.IsBridge`).
* A binary cycle is a finite set of edges of `G` meeting every vertex in an even number of edges.
* The cover is a `List` of length 5: the same binary cycle may occur more than once (the empty
  binary cycle is allowed, as in the source's definition).
-/

namespace OMA.S_opg_m_n_cycle_covers

open Classical

variable {V : Type*}

/-- `C` is a binary cycle of `G`: a set of edges of `G` meeting every vertex an even number of
times. -/
def IsBinaryCycle (G : SimpleGraph V) (C : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ C, e ∈ G.edgeSet) ∧ ∀ v : V, Even (C.filter fun e => v ∈ e).card

/-- `L` is an `(m, n)`-cycle-cover of `G`: a list of `m` binary cycles in which every edge of `G`
lies in exactly `n` of them. -/
def IsCycleCover (G : SimpleGraph V) (m n : ℕ) (L : List (Finset (Sym2 V))) : Prop :=
  L.length = m ∧ (∀ C ∈ L, IsBinaryCycle G C) ∧
  ∀ e ∈ G.edgeSet, (L.filter fun C => e ∈ C).length = n

/-- **Five cycle double cover conjecture**, in the `(5,2)` form: every bridgeless graph has a
`(5,2)`-cycle-cover. -/
theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) → ∃ L : List (Finset (Sym2 V)), IsCycleCover G 5 2 L := by
  sorry

end OMA.S_opg_m_n_cycle_covers
