import Mathlib

/-!
# Seagull problem

Source: https://www.openproblemgarden.org/op/seagull_problem (P. D. Seymour)
Credit: @k-okubo (agent: Claude Code, model claude-opus-5-5)

**Conjecture (Seymour).** Every `n` vertex graph with no independent set of size 3 has a complete graph
on `≥ n/2` vertices as a minor.

(It follows from Hadwiger's conjecture, since such a graph has chromatic number `≥ n/2`. The best known
bound is a complete minor on `≥ n/3` vertices; Kawarabayashi, Plummer and Toft improved this to
`≥ (n + ω(G))/3`.)

## Encoding

* `G` is a finite simple graph on `n = |V|` vertices (a minor of a graph is unchanged by deleting
  loops and merging parallel edges, and so is having an independent set of size 3).
* No independent set of size 3: no three distinct vertices are pairwise nonadjacent.
* `G` has `K_m` as a minor iff there are `m` pairwise disjoint, nonempty vertex sets (branch sets),
  each inducing a connected subgraph, with an edge of `G` between any two of them. This is the
  standard equivalent of obtaining `K_m` by deleting and contracting.
* `≥ n/2` is stated without division: `n ≤ 2 m`.
-/

namespace OMA.S_opg_seagull_problem

variable {V : Type*}

/-- `G` has the complete graph `K_m` as a minor, given by branch sets. -/
def HasCompleteMinor (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ B : Fin m → Set V,
    (∀ i, (B i).Nonempty ∧ (G.induce (B i)).Connected) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v)

/-- `G` has no independent set of size 3. -/
def NoIndepThree (G : SimpleGraph V) : Prop :=
  ∀ x y z : V, x ≠ y → y ≠ z → x ≠ z → G.Adj x y ∨ G.Adj y z ∨ G.Adj x z

/-- **Seagull conjecture**: an `n`-vertex graph with no independent set of size 3 has a complete
minor on at least `n / 2` vertices. -/
theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), NoIndepThree G →
      ∃ m : ℕ, Fintype.card V ≤ 2 * m ∧ HasCompleteMinor G m := by
  sorry

end OMA.S_opg_seagull_problem
