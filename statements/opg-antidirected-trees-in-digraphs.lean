import Mathlib

/-!
# Antidirected trees in digraphs

Source: https://www.openproblemgarden.org/op/antidirected_trees_in_digraphs
Credit: @shc261392

An antidirected tree is an orientation of a tree in which every vertex has either indegree `0`
or outdegree `0`.

Conjecture (Addario-Berry, Havet, Linhares Sales, Reed, Thomassé): let `D` be a digraph. If
`|A(D)| > (k - 2) |V(D)|`, then `D` contains every antidirected tree of order `k`.

Reading used here:
* A digraph is finite: a loopless relation `D : V → V → Prop` on a finite type `V` (no parallel
  arcs; both arcs `uv` and `vu` may be present). `|A(D)|` is the number of pairs `(u, v)` with
  `D u v`.
* An oriented tree of order `k` is a relation `T` on `Fin k` with no pair of opposite arcs whose
  underlying graph is a tree; it is antidirected when every vertex has no in-arc or no out-arc.
* Containing `T` means an injective `f : Fin k → V` sending every arc of `T` to an arc of `D`.
* `k ≥ 2` (the order of a tree with an arc; for `k = 1` the claim is trivial).
-/

namespace OMA.S_opg_antidirected_trees_in_digraphs

/-- `T` is an antidirected tree: an oriented tree in which every vertex is a source or a sink. -/
def IsAntidirectedTree {k : ℕ} (T : Fin k → Fin k → Prop) : Prop :=
  (∀ a b, T a b → ¬ T b a) ∧ (SimpleGraph.fromRel T).IsTree ∧
    ∀ a, (∀ b, ¬ T b a) ∨ (∀ b, ¬ T a b)

theorem main :
    ∀ k : ℕ, 2 ≤ k → ∀ (V : Type) [Fintype V] (D : V → V → Prop), (∀ v, ¬ D v v) →
      (k - 2) * Fintype.card V < {p : V × V | D p.1 p.2}.ncard →
        ∀ T : Fin k → Fin k → Prop, IsAntidirectedTree T →
          ∃ f : Fin k → V, Function.Injective f ∧ ∀ a b, T a b → D (f a) (f b) := by
  sorry

end OMA.S_opg_antidirected_trees_in_digraphs
