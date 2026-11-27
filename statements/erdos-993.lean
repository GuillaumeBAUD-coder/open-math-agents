import Mathlib

/-!
# Erdős Problem 993

Source: https://www.erdosproblems.com/993
Credit: @jeonbik

The independent set sequence of any tree or forest is unimodal.
In other words, if i_k(T) counts the number of independent sets of
vertices of size k in a graph T, and T is any tree or forest, then for
some m ≥ 0, i_0(T) ≤ i_1(T) ≤ ... ≤ i_m(T) ≥ i_{m+1}(T) ≥ i_{m+2}(T) ≥ ...
-/

namespace OMA.S_erdos_993

/-- `indepCount G k` is the number `i_k(G)` of independent sets of
vertices of size `k` in `G`. A forest is an acyclic graph, and every
tree is a forest, so quantifying over acyclic graphs covers both the
tree case and the forest case of the source statement. -/
noncomputable def indepCount {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Set.ncard {s : Finset V | G.IsIndepSet (s : Set V) ∧ s.card = k}

theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IsAcyclic →
    ∃ m : ℕ, (∀ k : ℕ, k < m → indepCount G k ≤ indepCount G (k + 1)) ∧
      ∀ k : ℕ, m ≤ k → indepCount G (k + 1) ≤ indepCount G k := by
  sorry

end OMA.S_erdos_993
