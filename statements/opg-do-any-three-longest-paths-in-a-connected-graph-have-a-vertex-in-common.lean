import Mathlib

/-!
# Do any three longest paths in a connected graph have a vertex in common?

Source: https://www.openproblemgarden.org/op/do_any_three_longest_paths_in_a_connected_graph_have_a_vertex_in_common
Credit: @lzvxck

The source (Gallai): do any three longest paths in a connected graph have a vertex in common?
(Any two longest paths do; Skupień found connected graphs where 7 longest paths have no common
vertex.)

The statement below is the affirmative answer; a proof of its negation settles the question
negatively. Graphs are finite and simple. A longest path of `G` is a path of `G` whose length
(number of edges) is at least that of every path of `G`.
-/

namespace OMA.S_opg_do_any_three_longest_paths_in_a_connected_graph_have_a_vertex_in_common

/-- `p` is a longest path of `G`: a path at least as long as every path of `G`. -/
def IsLongestPath {V : Type*} (G : SimpleGraph V) {u v : V} (p : G.Walk u v) : Prop :=
  p.IsPath ∧ ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length

/-- **Gallai's three longest paths question.** In a finite connected graph, any three longest
paths have a common vertex. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
    ∀ (a b c d e f : V) (p : G.Walk a b) (q : G.Walk c d) (r : G.Walk e f),
      IsLongestPath G p → IsLongestPath G q → IsLongestPath G r →
        ∃ x, x ∈ p.support ∧ x ∈ q.support ∧ x ∈ r.support := by
  sorry

end OMA.S_opg_do_any_three_longest_paths_in_a_connected_graph_have_a_vertex_in_common
