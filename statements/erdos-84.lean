import Mathlib

/-!
# Erdős Problem 84

Source: https://www.erdosproblems.com/84
Credit: @joshuadc11

The cycle set of a graph `G` on `n` vertices is the set `A ⊆ {3, ..., n}` of lengths of cycles
occurring in `G`. Let `f(n)` count the number of possible cycle sets of graphs on `n` vertices.
The first question (`f(n) = o(2^n)`) was proved by Verstraëte (2004). The remaining open
question is to prove that `f(n) / 2^(n/2) → ∞` as `n → ∞`.

Formalization notes:
- `cycleSet G` is the set of lengths of cycles (`G.Walk.IsCycle`) in a simple graph `G` on `Fin n`.
  Every cycle in a simple graph on `n` vertices automatically has length in `{3, ..., n}`.
- `numCycleSets n` is the cardinality (`Set.ncard`) of the finite set of all cycle sets achieved
  by simple graphs on `Fin n`.
-/

namespace OMA.S_erdos_84

/-- The cycle set of a simple graph `G` on `Fin n`: the set of all lengths of cycles in `G`. -/
def cycleSet {n : ℕ} (G : SimpleGraph (Fin n)) : Set ℕ :=
  {ℓ : ℕ | ∃ (v : Fin n) (p : G.Walk v v), p.IsCycle ∧ p.length = ℓ}

/-- The number `f(n)` of distinct cycle sets of simple graphs on `n` vertices. -/
noncomputable def numCycleSets (n : ℕ) : ℕ :=
  Set.ncard {A : Set ℕ | ∃ G : SimpleGraph (Fin n), cycleSet G = A}

theorem main :
    Filter.Tendsto
      (fun n : ℕ => (numCycleSets n : ℝ) / (2 : ℝ) ^ ((n : ℝ) / 2))
      Filter.atTop Filter.atTop := by
  sorry

end OMA.S_erdos_84
