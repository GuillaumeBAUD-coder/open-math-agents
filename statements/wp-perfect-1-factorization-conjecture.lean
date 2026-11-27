import Mathlib

/-!
# Perfect 1-factorization conjecture

Source: https://en.wikipedia.org/wiki/Graph_factorization#Perfect_1-factorization
Credit: @ihateSAS

The perfect 1-factorization conjecture: every complete graph on an even number
of vertices admits a perfect 1-factorization, i.e. a partition of its edge set
into `1`-factors (perfect matchings) such that the union of any two distinct
`1`-factors is a Hamiltonian cycle.

A complete graph on an even number of vertices has `2 * n` vertices with `n > 0`.
-/

namespace OMA.S_wp_perfect_1_factorization_conjecture

/-- A perfect `1`-factorization of `G`: a family of perfect matchings partitioning
the edge set of `G`, whose pairwise unions are Hamiltonian cycles. -/
structure IsPerfectOneFactorization {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ι : Type*) (F : ι → G.Subgraph) : Prop where
  isPerfectMatching : ∀ i, (F i).IsPerfectMatching
  edgeSet_pairwise_disjoint : Pairwise fun i j => Disjoint (F i).edgeSet (F j).edgeSet
  edgeSet_cover : ∀ e ∈ G.edgeSet, ∃ i, e ∈ (F i).edgeSet
  union_isHamiltonianCycle : ∀ i j, i ≠ j → ∃ (v : V) (c : G.Walk v v),
    c.IsHamiltonianCycle ∧
      ∀ e : Sym2 V, e ∈ c.edges ↔ e ∈ (F i).edgeSet ∪ (F j).edgeSet

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ (ι : Type) (F : ι → (⊤ : SimpleGraph (Fin (2 * n))).Subgraph),
        @IsPerfectOneFactorization (Fin (2 * n)) _ (Classical.decEq _) ⊤ (Classical.decRel _) ι F := by
  sorry

end OMA.S_wp_perfect_1_factorization_conjecture
