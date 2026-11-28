import Mathlib

/-!
# Gurvich's Δ-conjecture (1978)

Source: https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics (entry Delta-conjecture,
linked from https://en.wikipedia.org/wiki/complete_graph)
Credit: @johnkidenda

Consider a complete graph `(V; E_1, …, E_d)` each edge of which is colored by one of `d` colors such
that there exists a triangle `Δ` colored in three pairwise distinct colors. Then, in each chromatic
component `(V, E_i)`, `i = 1, …, d`, one can choose a maximal independent vertex-set such that the
intersection of the obtained `d` sets is empty.

References: V. Gurvich, On exact blockers and anti-blockers, Δ-conjecture, and related problems,
Discrete Applied Mathematics 159 (2011) 311–321; Andrade, Boros, Gurvich, in Optimization Problems
in Graph Theory (Springer, 2018) 3–64.

Conventions:
* `V` is finite, as in Gurvich's setting (the source speaks of a complete graph without saying so,
  but the conjecture is stated for finite graphs).
* The coloring is a symmetric map `c : V → V → Fin d`; only its values on pairs of distinct
  vertices matter. Colors need not all be used.
* The chromatic component `(V, E_i)` is the simple graph on all of `V` whose edges are the edges
  of color `i`. A maximal independent set is a `Maximal` element of `IsIndepSet` under inclusion.
-/

namespace OMA.S_wp_complete_graph

/-- The chromatic component `(V, E_i)`: the edges of the complete graph on `V` that have color `i`. -/
def colorGraph {V : Type} {d : ℕ} (c : V → V → Fin d) (i : Fin d) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => c u v = i

theorem main : ∀ (V : Type) [Finite V] (d : ℕ) (c : V → V → Fin d),
    (∀ u v, c u v = c v u) →
    (∃ a b e : V, a ≠ b ∧ b ≠ e ∧ a ≠ e ∧
      c a b ≠ c b e ∧ c b e ≠ c a e ∧ c a b ≠ c a e) →
    ∃ S : Fin d → Set V,
      (∀ i, Maximal (colorGraph c i).IsIndepSet (S i)) ∧ (⋂ i, S i) = ∅ := by
  sorry

end OMA.S_wp_complete_graph
