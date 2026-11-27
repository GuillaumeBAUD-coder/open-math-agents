import Mathlib

/-!
# Decomposing k-arc-strong tournament into k spanning strong digraphs

Source: https://www.openproblemgarden.org/op/decomposing_k_arc_strong_tournament_into_k_spanning_strong_digraphs
Credit: @shc261392

Conjecture (Bang-Jensen and Yeo): every `k`-arc-strong tournament decomposes into `k` spanning
strong digraphs.

Reading used here:
* A tournament on a finite type `V` is a relation `D` with no loops in which every two distinct
  vertices are joined by exactly one arc.
* `k`-arc-strong: after deleting any set of fewer than `k` arcs, every vertex still reaches every
  other vertex. `k ≥ 1`.
* A decomposition into `k` spanning strong digraphs is a partition of the arc set into `k`
  classes (a map `c` giving each arc `(a, b)` its class `c a b : Fin k`; only its values on arcs
  matter) such that, for each class `i`, the spanning subdigraph formed by the arcs of class `i`
  is strong: every vertex reaches every other vertex along arcs of class `i`.
-/

namespace OMA.S_opg_decomposing_k_arc_strong_tournament_into_k_spanning_strong_digraphs

/-- `D` is a tournament: loopless, and exactly one arc between any two distinct vertices. -/
def IsTournament {V : Type} (D : V → V → Prop) : Prop :=
  (∀ v, ¬ D v v) ∧ ∀ u v, u ≠ v → Xor' (D u v) (D v u)

/-- Every vertex reaches every vertex after deleting any fewer than `k` arcs. -/
def IsArcStrong {V : Type} (k : ℕ) (D : V → V → Prop) : Prop :=
  ∀ F : Finset (V × V), F.card < k →
    ∀ x y, Relation.ReflTransGen (fun a b => D a b ∧ (a, b) ∉ F) x y

theorem main :
    ∀ (V : Type) [Fintype V] (D : V → V → Prop) (k : ℕ), 1 ≤ k →
      IsTournament D → IsArcStrong k D →
        ∃ c : V → V → Fin k, ∀ i : Fin k, ∀ x y : V,
          Relation.ReflTransGen (fun a b => D a b ∧ c a b = i) x y := by
  sorry

end OMA.S_opg_decomposing_k_arc_strong_tournament_into_k_spanning_strong_digraphs
