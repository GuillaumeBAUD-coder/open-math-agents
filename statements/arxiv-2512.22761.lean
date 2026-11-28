import Mathlib

namespace OMA.S_arxiv_2512_22761

/-- A perfect matching of a finite simple graph `G` on `V` is a `Finset (Sym2 V)` of edges of `G`
such that every vertex `v : V` belongs to exactly one edge in `M`. -/
def IsPerfectMatching {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
  (∀ v : V, ∃! e ∈ M, v ∈ e)

/-- A subset `S ⊆ M` is a forcing set of a perfect matching `M` in `G` if `M` is the unique
perfect matching of `G` containing `S`. -/
def IsForcingSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (M S : Finset (Sym2 V)) : Prop :=
  IsPerfectMatching G M ∧ S ⊆ M ∧
  ∀ M' : Finset (Sym2 V), IsPerfectMatching G M' → S ⊆ M' → M' = M

/-- The forcing number `f(G, M)` of a perfect matching `M` in `G` is the minimum cardinality of
a forcing set of `M`. -/
noncomputable def forcingNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (M : Finset (Sym2 V)) : ℕ :=
  sInf { k : ℕ | ∃ S : Finset (Sym2 V), IsForcingSet G M S ∧ S.card = k }

/-- The minimum forcing number `f(G)` of `G` is the minimum of `f(G, M)` over all perfect
matchings `M` of `G`. -/
noncomputable def minForcingNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf { k : ℕ | ∃ M : Finset (Sym2 V), IsPerfectMatching G M ∧ forcingNumber G M = k }

/-- The maximum forcing number `F(G)` of `G` is the maximum of `f(G, M)` over all perfect
matchings `M` of `G`. -/
noncomputable def maxForcingNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ M : Finset (Sym2 V), IsPerfectMatching G M ∧ forcingNumber G M = k }

/-- A simple graph `G` is bipartite with bipartition `c : V → Bool` if every edge connects
vertices of opposite colors. -/
def IsBipartite {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ c : V → Bool, ∀ u v : V, G.Adj u v → c u ≠ c v

/-- Main theorems of Qianqian Liu, Ajit A. Diwan, and Heping Zhang (arXiv:2512.22761):
1. Theorem 3.1 / Corollary 3.2 (Confirming Conjecture 1.1 of Liu–Zhang): for any finite simple
   graph `G` of order `2n` with a perfect matching and `1 ≤ k ≤ n` with `F(G) ≥ n - k`,
   `k * e(G) ≥ n^2`, and equivalently `(n - F(G)) * e(G) ≥ n^2` (`F(G) ≤ n - n^2 / e(G)`).
2. Corollary 2.2 (`k = 1` case): for any bipartite graph `G` of order `2n` with a perfect matching
   and `F(G) ≥ n - 1`, `f(G) = n - 1` (in fact `G` is complete bipartite `K_{n, n}`).
3. Theorem 5.1 (`k = 2` case): for any bipartite graph `G` of order `2n` with a perfect matching
   and `F(G) = n - 2`, `f(G) ≥ ⌈n / 2⌉ - 1` (equivalently `2 * (f(G) + 1) ≥ n`). -/
theorem main :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n k : ℕ), Fintype.card V = 2 * n → 1 ≤ k → k ≤ n →
      (∃ M : Finset (Sym2 V), IsPerfectMatching G M) →
      n - k ≤ maxForcingNumber G →
      n ^ 2 ≤ k * G.edgeFinset.card) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n : ℕ), Fintype.card V = 2 * n → 1 ≤ n →
      (∃ M : Finset (Sym2 V), IsPerfectMatching G M) →
      n ^ 2 ≤ (n - maxForcingNumber G) * G.edgeFinset.card) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n : ℕ), Fintype.card V = 2 * n → 1 ≤ n →
      IsBipartite G → (∃ M : Finset (Sym2 V), IsPerfectMatching G M) →
      n - 1 ≤ maxForcingNumber G →
      minForcingNumber G = n - 1) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n : ℕ), Fintype.card V = 2 * n → 2 ≤ n →
      IsBipartite G → (∃ M : Finset (Sym2 V), IsPerfectMatching G M) →
      maxForcingNumber G = n - 2 →
      n ≤ 2 * (minForcingNumber G + 1)) := by sorry

end OMA.S_arxiv_2512_22761
