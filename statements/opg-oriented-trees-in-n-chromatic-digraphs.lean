import Mathlib

/-!
# Oriented trees in n-chromatic digraphs

Source: http://www.openproblemgarden.org/op/oriented_trees_in_n_chromatic_digraphs
Credit: @shc261392

Conjecture (Burr): every digraph with chromatic number at least `2k - 2` contains every
oriented tree of order `k` as a subdigraph.

Reading used here:
* A digraph on a vertex type `V` is a loopless relation `D : V → V → Prop` (`D u v` is an arc
  from `u` to `v`; both arcs `uv` and `vu` may be present). Its chromatic number is that of the
  underlying simple graph `SimpleGraph.fromRel D`.
* An oriented tree of order `k` is a relation `T` on `Fin k` with no pair of opposite arcs whose
  underlying graph is a tree.
* Containing `T` as a subdigraph means an injective map `f : Fin k → V` sending every arc of `T`
  to an arc of `D`.
* `k ≥ 2` (for `k = 1` the bound `2k - 2 = 0` would hold for the empty digraph, which contains no
  vertex; the conjecture is about `k ≥ 2`).
-/

namespace OMA.S_opg_oriented_trees_in_n_chromatic_digraphs

/-- `T` is an oriented tree: no two opposite arcs, and the underlying graph is a tree. -/
def IsOrientedTree {k : ℕ} (T : Fin k → Fin k → Prop) : Prop :=
  (∀ a b, T a b → ¬ T b a) ∧ (SimpleGraph.fromRel T).IsTree

theorem main :
    ∀ k : ℕ, 2 ≤ k → ∀ (V : Type) (D : V → V → Prop), (∀ v, ¬ D v v) →
      ((2 * k - 2 : ℕ) : ℕ∞) ≤ (SimpleGraph.fromRel D).chromaticNumber →
        ∀ T : Fin k → Fin k → Prop, IsOrientedTree T →
          ∃ f : Fin k → V, Function.Injective f ∧ ∀ a b, T a b → D (f a) (f b) := by
  sorry

end OMA.S_opg_oriented_trees_in_n_chromatic_digraphs
