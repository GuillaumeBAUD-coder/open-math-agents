import Mathlib

/-!
# Woodall's conjecture

Source: https://en.wikipedia.org/wiki/Woodall's_conjecture
Credit: @joshuadc11

In any finite directed graph (allowing parallel edges), the minimum number of edges in a
dicut equals the maximum number of pairwise disjoint dijoins; equivalently, if every dicut
contains at least `k` edges, then there exist `k` pairwise disjoint dijoins.

Formalization notes:
- A finite directed multigraph `D` on finite types `V` (vertices) and `E` (edges) is given
  by source and target maps `src tgt : E → V`.
- A dicut is the set of edges leaving a proper nonempty vertex subset `U` that has no
  incoming edges (`∀ e, D.src e ∉ U → D.tgt e ∉ U`).
- A dijoin is a set of edges `J : Set E` intersecting every dicut of `D`.
- Since any `k` disjoint dijoins force every dicut to have size at least `k`, the min-max
  equality is equivalent to: for every `k : ℕ`, if every dicut has cardinality at least `k`,
  then there exist `k` pairwise disjoint dijoins.
-/

namespace OMA.S_wp_woodall_s_conjecture

/-- A directed multigraph with vertex set `V` and edge set `E`. -/
structure Digraph (V E : Type*) where
  src : E → V
  tgt : E → V

/-- A dicut of `D`: the set of edges leaving a proper nonempty vertex subset `U`
that has no incoming edges. -/
def IsDicut {V E : Type*} (D : Digraph V E) (C : Set E) : Prop :=
  ∃ U : Set V, U.Nonempty ∧ Uᶜ.Nonempty ∧
    (∀ e : E, D.src e ∉ U → D.tgt e ∉ U) ∧
    C = {e : E | D.src e ∈ U ∧ D.tgt e ∉ U}

/-- A dijoin of `D`: a set of edges that intersects every dicut of `D`. -/
def IsDijoin {V E : Type*} (D : Digraph V E) (J : Set E) : Prop :=
  ∀ C : Set E, IsDicut D C → (J ∩ C).Nonempty

theorem main :
    ∀ (V E : Type*) [Fintype V] [Fintype E] (D : Digraph V E) (k : ℕ),
      (∀ C : Set E, IsDicut D C → k ≤ Set.ncard C) →
      ∃ J : Fin k → Set E,
        (∀ i, IsDijoin D (J i)) ∧
        Pairwise (fun i j => Disjoint (J i) (J j)) := by
  sorry

end OMA.S_wp_woodall_s_conjecture
