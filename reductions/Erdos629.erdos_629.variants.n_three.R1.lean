import FormalConjectures.ErdosProblems.«629»

-- Reduction Erdos629.erdos_629.variants.n_three.R1 of n(3) = 14
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `n(3) = 14`, split into its two inequalities

`n(k)` is the least number of vertices of a bipartite graph whose list chromatic number exceeds `k`.
Hanson, MacGillivray and Toft proved `n(3) = 14` by establishing two separate facts.

* `H1` is the upper bound: there is a bipartite graph on `14` vertices whose list chromatic number
  is greater than `3`.  This is a construction, checked on one explicit graph.
* `H2` is the lower bound: no bipartite graph on at most `13` vertices has list chromatic number
  greater than `3`.  This is the exhaustive part of the argument.

The two halves are of different natures (one witness versus a statement about all small graphs), and
together they pin down the value.
-/

namespace OMA.R_Erdos629_erdos_629_variants_n_three_R1

/-- The upper bound: a bipartite graph on `14` vertices with list chromatic number exceeding `3`
exists. -/
def H1 : Prop :=
  Erdos629.n 3 ≤ 14

/-- The lower bound: every bipartite graph with list chromatic number exceeding `3` has at least
`14` vertices. -/
def H2 : Prop :=
  14 ≤ Erdos629.n 3

theorem main : H1 → H2 → type_of% @Erdos629.erdos_629.variants.n_three := by
  intro h1 h2
  exact le_antisymm h1 h2

end OMA.R_Erdos629_erdos_629_variants_n_three_R1
