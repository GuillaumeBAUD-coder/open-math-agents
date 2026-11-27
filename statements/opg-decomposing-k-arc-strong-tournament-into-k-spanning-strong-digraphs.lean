import Mathlib

/-!
# Decomposing k-arc-strong tournament into k spanning strong digraphs

Source: https://www.openproblemgarden.org/op/decomposing_k_arc_strong_tournament_into_k_spanning_strong_digraphs
Credit: @ishaanzee

**Conjecture** (J. Bang-Jensen, A. Yeo). Every `k`-arc-strong tournament decomposes into `k`
spanning strong digraphs.

(It implies Kelly's conjecture on Hamiltonian decompositions of regular tournaments.)

Formalization:
* A tournament on a finite set `V` is a relation `T` with no loops and exactly one of `T u v`,
  `T v u` for distinct `u`, `v`.
* A digraph on `V` is strong (strongly connected) if every vertex reaches every other vertex by a
  directed path (`Relation.ReflTransGen`).
* `T` is `k`-arc-strong if it remains strong after deleting any set of fewer than `k` arcs.
* A decomposition into `k` spanning strong digraphs assigns each arc of `T` one of `k` classes
  (`col : V → V → Fin k`) so that, for every class `i`, the digraph on all of `V` formed by the arcs
  of class `i` is strong. We take `k ≥ 1`.
-/

namespace OMA.S_opg_decomposing_k_arc_strong_tournament_into_k_spanning_strong_digraphs

/-- The digraph `D` on `V` is strongly connected. -/
def IsStrong {V : Type*} (D : V → V → Prop) : Prop := ∀ x y : V, Relation.ReflTransGen D x y

/-- **Bang-Jensen–Yeo conjecture.** -/
theorem main : ∀ (k : ℕ) (V : Type) [Fintype V] [DecidableEq V] (T : V → V → Prop), 1 ≤ k →
    (∀ v, ¬ T v v) → (∀ u v, u ≠ v → (T u v ↔ ¬ T v u)) →
    (∀ F : Finset (V × V), F.card < k → IsStrong fun a b => T a b ∧ (a, b) ∉ F) →
      ∃ col : V → V → Fin k, ∀ i : Fin k, IsStrong fun a b => T a b ∧ col a b = i := by
  sorry

end OMA.S_opg_decomposing_k_arc_strong_tournament_into_k_spanning_strong_digraphs
