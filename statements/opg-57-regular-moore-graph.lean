import Mathlib

/-!
# 57-regular Moore graph?

Source: https://www.openproblemgarden.org/op/57_regular_moore_graph
Credit: @lzvxck

The source asks: does there exist a 57-regular graph with diameter 2 and girth 5?

(Hoffman and Singleton proved that an `r`-regular Moore graph of diameter 2 has
`r ∈ {2, 3, 7, 57}`; the cases 2, 3, 7 exist and are unique, the case 57 is open.)
The statement below is the affirmative answer; a proof of its negation settles the question
negatively. Such a graph is necessarily finite (a 57-regular graph of diameter 2 has at most
`1 + 57 + 57 * 56` vertices), so the vertex type is taken finite. Diameter and girth are the
extended-valued `ediam` and `egirth` of Mathlib, so `ediam = 2` includes connectedness.
-/

namespace OMA.S_opg_57_regular_moore_graph

/-- **The 57-regular Moore graph.** There is a 57-regular graph with diameter 2 and girth 5. -/
theorem main : ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    G.IsRegularOfDegree 57 ∧ G.ediam = 2 ∧ G.egirth = 5 := by
  sorry

end OMA.S_opg_57_regular_moore_graph
