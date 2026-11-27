import Mathlib

/-!
# Erdős Problem 993

Source: https://www.erdosproblems.com/993
Credit: @mattdorman

The source states (a question of Alavi, Malde, Schwenk and Erdős): the independent set sequence
of any tree or forest is unimodal. That is, if `i_k(G)` counts the independent sets of vertices
of size `k` in a graph `G`, and `T` is any tree or forest, then for some `m ≥ 0`,
`i₀(T) ≤ i₁(T) ≤ ⋯ ≤ i_m(T) ≥ i_{m+1}(T) ≥ i_{m+2}(T) ≥ ⋯`.

Reading used here: trees and forests are the finite acyclic simple graphs (`SimpleGraph.IsAcyclic`
covers both). `i_k(T)` is the number of `k`-element vertex sets that are independent in `T`.
-/

namespace OMA.S_erdos_993

open Classical in
/-- The number of independent sets of size `k` in `G`. -/
noncomputable def indepSetCount {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : ℕ :=
  ((Finset.univ : Finset V).powersetCard k |>.filter fun s => G.IsIndepSet (s : Set V)).card

theorem main :
    ∀ (V : Type) [Fintype V] (T : SimpleGraph V), T.IsAcyclic →
      ∃ m : ℕ, (∀ k < m, indepSetCount T k ≤ indepSetCount T (k + 1)) ∧
        ∀ k, m ≤ k → indepSetCount T (k + 1) ≤ indepSetCount T k := by
  sorry

end OMA.S_erdos_993
