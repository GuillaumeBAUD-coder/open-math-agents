import Mathlib

/-!
# 1-factorization conjecture

Source: https://en.wikipedia.org/wiki/Graph_factorization#1-factorization_conjecture
Credit: @lzvxck

The source states: if `n` is odd and `k ≥ n`, or `n` is even and `k ≥ n - 1`, then every
`k`-regular graph with `2n` vertices is 1-factorable.

A 1-factor of `G` is a perfect matching of `G`, and a 1-factorization of `G` is a partition of
the edge set of `G` into disjoint 1-factors (Wikipedia, Graph factorization). `G` is
1-factorable if it has a 1-factorization.
-/

namespace OMA.S_wp_1_factorization_conjecture

/-- `G` is 1-factorable: its edges are partitioned into perfect matchings, i.e. there is a
family `F` of perfect matchings of `G` such that every edge of `G` lies in exactly one member
of `F`. -/
def IsOneFactorable {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ F : Set G.Subgraph, (∀ M ∈ F, M.IsPerfectMatching) ∧
    ∀ e ∈ G.edgeSet, ∃! M, M ∈ F ∧ e ∈ M.edgeSet

/-- **1-factorization conjecture.** If `n` is odd and `k ≥ n`, or `n` is even and
`k ≥ n - 1`, then every `k`-regular graph on `2n` vertices is 1-factorable. -/
theorem main : ∀ (n k : ℕ), (Odd n ∧ n ≤ k) ∨ (Even n ∧ n - 1 ≤ k) →
    ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = 2 * n →
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.IsRegularOfDegree k →
        IsOneFactorable G := by
  sorry

end OMA.S_wp_1_factorization_conjecture
