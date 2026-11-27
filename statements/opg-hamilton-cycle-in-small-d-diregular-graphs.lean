import Mathlib

/-!
# Hamilton cycle in small d-diregular graphs

Source: https://www.openproblemgarden.org/op/hamilton_cycle_in_small_d_diregular_graphs
(B. Jackson)
Credit: @ishaanzee

A directed graph is `k`-diregular if every vertex has indegree and outdegree at least `k`.

**Conjecture.** For `d > 2`, every `d`-diregular oriented graph on at most `4d + 1` vertices has a
Hamilton cycle.

(The disjoint union of two regular tournaments on `2d + 1` vertices shows that this would be best
possible.)

Formalization: an oriented graph on a finite set `V` is a relation `D` with no loops and no
2-cycles (`D u v → ¬ D v u`). A Hamilton cycle visits every vertex exactly once and returns to its
start: an enumeration `e : Fin n ≃ V` of the `n = |V|` vertices with an arc from `e i` to
`e (i + 1 mod n)` for every `i` (`finRotate`).
-/

namespace OMA.S_opg_hamilton_cycle_in_small_d_diregular_graphs

/-- **Jackson's conjecture.** -/
theorem main : ∀ (d : ℕ) (V : Type) [Fintype V] [DecidableEq V] (D : V → V → Prop) [DecidableRel D],
    2 < d → (∀ v, ¬ D v v) → (∀ u v, D u v → ¬ D v u) →
    (∀ v, d ≤ (Finset.univ.filter fun w => D v w).card) →
    (∀ v, d ≤ (Finset.univ.filter fun w => D w v).card) →
    Fintype.card V ≤ 4 * d + 1 →
      ∃ e : Fin (Fintype.card V) ≃ V, ∀ i, D (e i) (e (finRotate _ i)) := by
  sorry

end OMA.S_opg_hamilton_cycle_in_small_d_diregular_graphs
