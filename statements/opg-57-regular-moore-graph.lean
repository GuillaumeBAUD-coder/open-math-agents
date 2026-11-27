import Mathlib

/-!
# 57-regular Moore graph?

Source: https://www.openproblemgarden.org/op/57_regular_moore_graph
Credit: @biondadave

Question (Hoffman–Singleton): Does there exist a 57-regular graph with diameter 2 and girth 5?

The question is open, so `main` states the existence assertion; resolving the problem means
proving `main` or its negation.

Conventions:
- The vertex type is finite. This loses nothing: a 57-regular graph of diameter 2 has at most
  `1 + 57 + 57 * 56 = 3250` vertices (and a Moore graph has exactly that many).
- Diameter and girth use Mathlib's extended versions `SimpleGraph.ediam` and
  `SimpleGraph.egirth` (values in `ℕ∞`), so `ediam = 2` forces the graph to be connected and
  `egirth = 5` forces it to contain a cycle, with no `0`-for-undefined convention involved.
-/

namespace OMA.S_opg_57_regular_moore_graph

theorem main :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.IsRegularOfDegree 57 ∧ G.ediam = 2 ∧ G.egirth = 5 := by
  sorry

end OMA.S_opg_57_regular_moore_graph
