import FormalConjectures.Wikipedia.TotalColoringConjecture

-- Reduction TotalColoringConjecture.total_coloring_conjecture.variants.maxDegree_le_five.R1 of the total colouring conjecture, maxDegree le five
-- Credit: @cosmaticdev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Total colouring conjecture for maximum degree at most 5: reduction by the degree range

The known proofs split by maximum degree: Rosenfeld and Vijayaditya cover $\Delta \le 3$, and
Kostochka covers $\Delta = 4, 5$. H1 and H2 below are exactly those two ranges; main is the
case split $\Delta \le 3$ versus $4 \le \Delta \le 5$.
-/

namespace OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1

open SimpleGraph

/-- The total colouring conjecture for graphs of maximum degree at most 3
(Rosenfeld, Vijayaditya). -/
def H1 : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.maxDegree ≤ 3 → G.totalChromaticNumber ≤ G.maxDegree + 2

/-- The total colouring conjecture for graphs of maximum degree 4 or 5 (Kostochka). -/
def H2 : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    4 ≤ G.maxDegree → G.maxDegree ≤ 5 → G.totalChromaticNumber ≤ G.maxDegree + 2

theorem main : H1 → H2 → type_of% @TotalColoringConjecture.total_coloring_conjecture.variants.maxDegree_le_five := by
  intro h1 h2 V _ _ G _ hΔ
  by_cases h3 : G.maxDegree ≤ 3
  · exact h1 G h3
  · exact h2 G (by omega) hΔ

end OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1
