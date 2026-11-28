import Mathlib

/-!
# Second neighborhood problem (Seymour's second neighborhood conjecture)

Source: https://en.wikipedia.org/wiki/second_neighborhood_problem
Credit: @joshuadc11

Does every finite nonempty oriented graph contain a vertex `v` for which there are at least
as many vertices at directed distance two from `v` as at directed distance one from `v`?

Formalization notes:
- An oriented graph on a finite nonempty vertex type `V` is given by an asymmetric relation
  `adj : V → V → Prop` (`∀ u v, adj u v → ¬ adj v u`, which excludes both self-loops and
  antiparallel edges).
- `firstNeighborhood adj v` is the set of vertices at directed distance `1` from `v`, and
  `secondNeighborhood adj v` is the set of vertices `w ≠ v` not at distance `1` that are
  reachable from `v` in two directed steps.
-/

namespace OMA.S_wp_second_neighborhood_problem

/-- The first out-neighborhood `N⁺(v)`: vertices at directed distance `1` from `v`. -/
def firstNeighborhood {V : Type*} (adj : V → V → Prop) (v : V) : Set V :=
  {u : V | adj v u}

/-- The second out-neighborhood `N⁺⁺(v)`: vertices at directed distance `2` from `v`. -/
def secondNeighborhood {V : Type*} (adj : V → V → Prop) (v : V) : Set V :=
  {w : V | w ≠ v ∧ ¬ adj v w ∧ ∃ u : V, adj v u ∧ adj u w}

theorem main :
    ∀ (V : Type*) [Fintype V] [Nonempty V] (adj : V → V → Prop),
      (∀ u v, adj u v → ¬ adj v u) →
      ∃ v : V,
        Set.ncard (firstNeighborhood adj v) ≤ Set.ncard (secondNeighborhood adj v) := by
  sorry

end OMA.S_wp_second_neighborhood_problem
