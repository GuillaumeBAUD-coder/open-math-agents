import Mathlib

/-!
# Arc-disjoint out-branching and in-branching

Source: https://www.openproblemgarden.org/op/arc_disjoint_out_branching_and_in_branching
Credit: @shc261392

Conjecture (Thomassen): there exists an integer `k` such that every `k`-arc-strong digraph `D`
with specified vertices `u` and `v` contains an out-branching rooted at `u` and an in-branching
rooted at `v` which are arc-disjoint.

Reading used here:
* A digraph is a loopless relation `D : V → V → Prop` on a finite type `V` (no parallel arcs).
  `k`-arc-strong: after deleting any set of fewer than `k` arcs, every vertex still reaches every
  other vertex.
* An out-branching rooted at `u` is a set `B` of arcs of `D` forming a spanning tree directed
  away from `u`: `u` has no in-arc in `B`, every other vertex has exactly one in-arc in `B`, and
  every vertex is reached from `u` along arcs of `B`. An in-branching rooted at `v` is the same
  with all arcs reversed.
* `u` and `v` are arbitrary vertices (they may coincide).
-/

namespace OMA.S_opg_arc_disjoint_out_branching_and_in_branching

/-- Every vertex reaches every vertex after deleting any fewer than `k` arcs. -/
def IsArcStrong {V : Type} (k : ℕ) (D : V → V → Prop) : Prop :=
  ∀ F : Finset (V × V), F.card < k →
    ∀ x y, Relation.ReflTransGen (fun a b => D a b ∧ (a, b) ∉ F) x y

/-- `B` is an out-branching of `D` rooted at `u`. -/
def IsOutBranching {V : Type} (D : V → V → Prop) (u : V) (B : Set (V × V)) : Prop :=
  (∀ p ∈ B, D p.1 p.2) ∧ (∀ y, (y, u) ∉ B) ∧ (∀ x, x ≠ u → ∃! y, (y, x) ∈ B) ∧
    ∀ x, Relation.ReflTransGen (fun a b => (a, b) ∈ B) u x

/-- `B` is an in-branching of `D` rooted at `v`. -/
def IsInBranching {V : Type} (D : V → V → Prop) (v : V) (B : Set (V × V)) : Prop :=
  (∀ p ∈ B, D p.1 p.2) ∧ (∀ y, (v, y) ∉ B) ∧ (∀ x, x ≠ v → ∃! y, (x, y) ∈ B) ∧
    ∀ x, Relation.ReflTransGen (fun a b => (a, b) ∈ B) x v

theorem main :
    ∃ k : ℕ, ∀ (V : Type) [Fintype V] (D : V → V → Prop), (∀ v, ¬ D v v) → IsArcStrong k D →
      ∀ u v : V, ∃ B₁ B₂ : Set (V × V),
        IsOutBranching D u B₁ ∧ IsInBranching D v B₂ ∧ Disjoint B₁ B₂ := by
  sorry

end OMA.S_opg_arc_disjoint_out_branching_and_in_branching
