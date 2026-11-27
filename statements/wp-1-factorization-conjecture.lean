import Mathlib

/-!
# The 1-factorization conjecture

Source: https://en.wikipedia.org/wiki/Graph_factorization#1-factorization_conjecture
Credit: @Andyi955

A 1-factor of a graph is a perfect matching, i.e. a set of edges meeting every vertex exactly once,
and a 1-factorization of a `k`-regular graph is a partition of its edge set into `k` 1-factors;
equivalently it is a proper edge colouring with `k` colours (Wikipedia, Graph factorization).

The 1-factorization conjecture states: let `G` be a `k`-regular graph with `2 * n` nodes; if `n` is
odd and `k ≥ n`, or if `n` is even and `k ≥ n - 1`, then `G` is 1-factorable. Csaba, Kuhn, Lo,
Osthus and Treglown (2016) proved it for all sufficiently large `n`; the statement for arbitrary
`n`, which is `main` below, is the conjecture recorded as open.

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s on a vertex type `V` with `Fintype.card V = 2 * n`.
* `k`-regular means `G.IsRegularOfDegree k`.
* `IsOneFactorization G k` says the edge set of `G` is partitioned into `k` subgraphs, each of them
  a perfect matching (`SimpleGraph.Subgraph.IsPerfectMatching`); this is the definition of
  `k`-factorable, i.e. 1-factorable since `G` is `k`-regular.
* The two branches of the source statement are kept verbatim, as the two arms of a disjunction;
  `n - 1` is truncated subtraction, and the branch is only invoked under `Even n`, where `n ≥ 1`
  makes it the intended `n - 1`.
-/

namespace OMA.S_wp_1_factorization_conjecture

/-- `IsOneFactorization G k` holds when the edge set of `G` is partitioned into `k` perfect
matchings (1-factors): there is a family `M : Fin k → G.Subgraph` of perfect matchings of `G` such
that every edge of `G` lies in exactly one member of the family. Equivalently (Wikipedia, Graph
factorization) `G` is properly edge-colourable with `k` colours. -/
def IsOneFactorization {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ M : Fin k → G.Subgraph,
    (∀ i : Fin k, (M i).IsPerfectMatching) ∧
      ∀ e ∈ G.edgeSet, ∃! i : Fin k, e ∈ (M i).edgeSet

/-- **1-factorization conjecture**: if `n` is odd and `k ≥ n`, or if `n` is even and `k ≥ n - 1`,
then every `k`-regular graph with `2 * n` vertices is 1-factorable. -/
theorem main : ∀ (n k : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj],
    Fintype.card V = 2 * n → G.IsRegularOfDegree k →
      ((Odd n ∧ n ≤ k) ∨ (Even n ∧ n - 1 ≤ k)) → IsOneFactorization G k := by
  sorry

end OMA.S_wp_1_factorization_conjecture
