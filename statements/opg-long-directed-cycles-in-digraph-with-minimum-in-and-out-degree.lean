import Mathlib

/-!
# Long directed cycles in diregular digraphs

Source: https://www.openproblemgarden.org/op/long_directed_cycles_in_digraph_with_minimum_in_and_out_degree
Credit: @shc261392

Conjecture (Jackson): every strong oriented graph in which each vertex has indegree and
outdegree at least `d` contains a directed cycle of length at least `2d + 1`.

Reading used here:
* An oriented graph on a finite nonempty vertex type `V` is a relation `D` with no loops and no
  pair of opposite arcs. Strong (strongly connected): every vertex reaches every other along
  arcs, `Relation.ReflTransGen D u v`.
* The outdegree of `v` is the number of `w` with `D v w`, the indegree the number of `w` with
  `D w v`.
* A directed cycle of length `ℓ` is an injective `c : Fin ℓ → V` with an arc from `c i` to
  `c (i + 1)` for every `i`, indices taken cyclically (`finRotate ℓ`).
* `d ≥ 1` (for `d = 0` a single vertex is a strong oriented graph without cycles).
-/

namespace OMA.S_opg_long_directed_cycles_in_digraph_with_minimum_in_and_out_degree

theorem main :
    ∀ (V : Type) [Fintype V] [Nonempty V] (D : V → V → Prop) (d : ℕ), 1 ≤ d →
      (∀ v, ¬ D v v) → (∀ u v, D u v → ¬ D v u) →
      (∀ u v, Relation.ReflTransGen D u v) →
      (∀ v, d ≤ {w | D v w}.ncard ∧ d ≤ {w | D w v}.ncard) →
        ∃ ℓ : ℕ, 2 * d + 1 ≤ ℓ ∧ ∃ c : Fin ℓ → V, Function.Injective c ∧
          ∀ i : Fin ℓ, D (c i) (c (finRotate ℓ i)) := by
  sorry

end OMA.S_opg_long_directed_cycles_in_digraph_with_minimum_in_and_out_degree
