import Mathlib

/-!
# 1-factorization conjecture

Source: https://en.wikipedia.org/wiki/Graph_factorization#1-factorization_conjecture
Credit: @ihateSAS

A 1-factor of a graph is a perfect matching, that is, a spanning 1-regular subgraph; a graph is
1-factorable when its edges can be partitioned into 1-factors, equivalently when it admits a proper
edge colouring with as many colours as its degree.

The 1-factorization conjecture of Chetwynd and Hilton states: let `G` be a `k`-regular graph with
`2n` nodes. If `n` is odd and `k ≥ n`, then `G` is 1-factorable; if `n` is even and `k ≥ n - 1`,
then `G` is 1-factorable. The conjecture was confirmed for sufficiently large `n` by Csaba, Kühn,
Lo, Osthus and Treglown, *Proof of the 1-factorization and Hamilton decomposition conjectures*,
Memoirs of the AMS 1154 (2016).

The source states the two parity cases separately; they are recorded here as two implications under
one theorem, with the same quantifiers and the same ranges.
-/

namespace OMA.S_wp_1_factorization_conjecture

/-- `G` is 1-factorable: there is a family of perfect matchings of `G` (its 1-factors) such that
every edge of `G` lies in exactly one member of the family. -/
def IsOneFactorable {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (F : ι → G.Subgraph),
    (∀ i, (F i).IsPerfectMatching) ∧ ∀ e ∈ G.edgeSet, ∃! i, e ∈ (F i).edgeSet

/-- **1-factorization conjecture** (Chetwynd--Hilton): a `k`-regular graph on `2n` vertices is
1-factorable if `n` is odd and `k ≥ n`, and if `n` is even and `k ≥ n - 1`. -/
theorem main :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (n k : ℕ),
      Fintype.card V = 2 * n → G.IsRegularOfDegree k →
      (Odd n → n ≤ k) → (Even n → n - 1 ≤ k) → IsOneFactorable G := by
  sorry

end OMA.S_wp_1_factorization_conjecture
