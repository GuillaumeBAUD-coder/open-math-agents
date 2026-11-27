import Mathlib

/-!
# Arc-disjoint directed cycles in regular directed graphs

Source: https://www.openproblemgarden.org/op/arc_disjoint_directed_cycles_in_regular_directed_graphs
Credit: @shc261392

Conjecture (Alon, McDiarmid and Molloy): if `G` is a `k`-regular directed graph with no
parallel arcs, then `G` contains a collection of `(k + 1).choose 2` arc-disjoint directed cycles.

Reading used here:
* A directed graph with no parallel arcs is a loopless relation `D : V → V → Prop` on a finite
  type `V` (both arcs `uv` and `vu` may be present, as in the complete symmetric digraph that
  shows the bound is best possible). `k`-regular: every vertex has indegree and outdegree `k`.
* A directed cycle of length `ℓ ≥ 2` is an injective `c : Fin ℓ → V` with an arc from `c i` to
  `c (i + 1)` for every `i`, indices taken cyclically (`finRotate ℓ`); its arcs are the pairs
  `(c i, c (i + 1))`.
* The collection is indexed by `Fin ((k + 1).choose 2)`; arc-disjoint means that an arc used by
  two members of the collection forces them to be the same member.
-/

namespace OMA.S_opg_arc_disjoint_directed_cycles_in_regular_directed_graphs

theorem main :
    ∀ (V : Type) [Fintype V] (D : V → V → Prop) (k : ℕ), (∀ v, ¬ D v v) →
      (∀ v, {w | D v w}.ncard = k ∧ {w | D w v}.ncard = k) →
        ∃ (len : Fin ((k + 1).choose 2) → ℕ) (c : ∀ j, Fin (len j) → V),
          (∀ j, 2 ≤ len j ∧ Function.Injective (c j) ∧
            ∀ i, D (c j i) (c j (finRotate (len j) i))) ∧
          ∀ j j' i i', c j i = c j' i' → c j (finRotate (len j) i) = c j' (finRotate (len j') i') →
            j = j' := by
  sorry

end OMA.S_opg_arc_disjoint_directed_cycles_in_regular_directed_graphs
