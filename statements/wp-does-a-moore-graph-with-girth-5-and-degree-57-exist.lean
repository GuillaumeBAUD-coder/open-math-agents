import Mathlib

/-!
Does a Moore graph of girth 5 and degree 57 exist?

Source: https://en.wikipedia.org/wiki/Moore_graph
Credit: @Tchikrazi
-/

namespace OMA.S_wp_does_a_moore_graph_with_girth_5_and_degree_57_exist

/-- The equivalent strongly regular graph parameters are (3250, 57, 0, 1):
57 neighbors per vertex, no common neighbor for adjacent vertices, and
exactly one common neighbor for nonadjacent distinct vertices. -/
theorem main :
    ∃ G : SimpleGraph (Fin 3250),
      (∀ v, {w | G.Adj v w}.ncard = 57) ∧
      (∀ u v, G.Adj u v → ¬ ∃ w, G.Adj u w ∧ G.Adj v w) ∧
      ∀ u v, u ≠ v → ¬ G.Adj u v → ∃! w, G.Adj u w ∧ G.Adj v w := by
  sorry

end OMA.S_wp_does_a_moore_graph_with_girth_5_and_degree_57_exist
