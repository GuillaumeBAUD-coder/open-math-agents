import Mathlib

/-!
# Erdős Problem 149

Source: https://www.erdosproblems.com/149
Credit: @mattdorman

The source asks (Erdős and Nešetřil): the strong chromatic index `sq(G)` of a graph `G` is the
minimum `k` such that the edges of `G` can be partitioned into `k` sets of strongly independent
edges, that is, sets whose induced subgraph is a union of vertex-disjoint edges. Is it true that,
for any graph `G` with maximum degree `Δ`, `sq(G) ≤ (5/4) Δ²`?

Reading used here: `G` is a finite simple graph and `Δ = G.maxDegree`. A set `S` of edges induces
a union of vertex-disjoint edges exactly when any two distinct edges of `S` share no vertex and
no edge of `G` joins a vertex of one to a vertex of the other. So `sq(G) ≤ (5/4) Δ²` says: there
is `k ≤ (5/4) Δ²` and a colouring of the edges with `k` colours in which any two distinct edges of
the same colour are separated in that sense. The statement below is the affirmative answer.
-/

namespace OMA.S_erdos_149

/-- Two edges are strongly separated in `G`: no shared vertex and no edge of `G` between them. -/
def StronglySeparated {V : Type} (G : SimpleGraph V) (e f : Sym2 V) : Prop :=
  ∀ u ∈ e, ∀ v ∈ f, u ≠ v ∧ ¬ G.Adj u v

theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      ∃ k : ℕ, (k : ℝ) ≤ 5 / 4 * (G.maxDegree : ℝ) ^ 2 ∧
        ∃ c : G.edgeSet → Fin k, ∀ e f : G.edgeSet, e ≠ f → c e = c f →
          StronglySeparated G e.1 f.1 := by
  sorry

end OMA.S_erdos_149
