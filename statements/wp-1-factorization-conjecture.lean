import Mathlib

/-!
# 1-factorization conjecture

Source: https://en.wikipedia.org/wiki/Graph_factorization#1-factorization_conjecture
Source text license: CC BY-SA 4.0
Credit: @menelikbaye-digitalmethod

The factors below are spanning perfect matchings of the original graph.
Every edge belongs to exactly one factor, expressing an edge partition.
The parity conditions retain the two degree thresholds stated by the source.
-/

namespace OMA.S_wp_1_factorization_conjecture

theorem main :
    ∀ (n k : ℕ) (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj],
      G.IsRegularOfDegree k →
      ((Odd n ∧ n ≤ k) ∨ (Even n ∧ n - 1 ≤ k)) →
      ∃ M : Fin k → G.Subgraph,
        (∀ i, (M i).IsPerfectMatching) ∧
        ∀ e ∈ G.edgeSet, ∃! i : Fin k, e ∈ (M i).edgeSet := by
  sorry

end OMA.S_wp_1_factorization_conjecture
