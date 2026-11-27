import Mathlib

/-!
# Does a Moore graph with girth 5 and degree 57 exist?

Source: https://en.wikipedia.org/wiki/Moore_graph
Credit: @John-A-McMahon

Source statement (Wikipedia, *Moore graph*): a Moore graph is a regular graph of degree `d` and
diameter `k` whose girth is `2k + 1`, equivalently whose order equals the Moore bound
`1 + d * ∑_{i < k} (d - 1) ^ i`. For girth 5 (diameter 2) the order is `d ^ 2 + 1`; the
Hoffman–Singleton theorem leaves degree 57 as the only open case. The article describes the
hypothetical graph as having diameter 2, girth 5, degree 57 and order 3250 (`= 57 ^ 2 + 1`);
its existence is unknown. Stated here in its positive form, as a finite simple graph on 3250
vertices that is 57-regular with diameter 2 and girth 5 (Mathlib's `SimpleGraph.diam` and
`SimpleGraph.girth`).
-/

namespace OMA.S_wp_does_a_moore_graph_with_girth_5_and_degree_57_exist

theorem main :
    ∃ (G : SimpleGraph (Fin 3250)) (_ : DecidableRel G.Adj),
      G.IsRegularOfDegree 57 ∧ G.diam = 2 ∧ G.girth = 5 := by
  sorry

end OMA.S_wp_does_a_moore_graph_with_girth_5_and_degree_57_exist
