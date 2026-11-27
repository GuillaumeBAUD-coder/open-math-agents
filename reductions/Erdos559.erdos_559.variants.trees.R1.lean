import FormalConjectures.ErdosProblems.«559»

-- Reduction Erdos559.erdos_559.variants.trees.R1 of Erdős Problem 559 — trees
-- Credit: @cosmaticdev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 559, bounded-degree trees: reduction by the degree bound

Friedman and Pippenger [FrPi87] proved the linear bound on the size Ramsey number of trees with
bounded maximum degree. H1 is the trivial range `d ≤ 1` (the only trees of maximum degree at
most 1 are the single vertex and the single edge), and H2 is the Friedman–Pippenger range
`d ≥ 2`; main is the case split on `d`.
-/

namespace OMA.R_Erdos559_erdos_559_variants_trees_R1

open SimpleGraph

open scoped Classical in
/-- The trivial degree range `d ≤ 1`. -/
def H1 : Prop := ∀ d : ℕ, d ≤ 1 → ∃ C : ℝ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.IsTree → G.maxDegree ≤ d → (sizeRamsey G G : ℝ) ≤ C * Fintype.card V

open scoped Classical in
/-- The Friedman–Pippenger range `d ≥ 2`. -/
def H2 : Prop := ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.IsTree → G.maxDegree ≤ d → (sizeRamsey G G : ℝ) ≤ C * Fintype.card V

theorem main : H1 → H2 → type_of% @Erdos559.erdos_559.variants.trees := by
  intro h1 h2 d
  by_cases hd : d ≤ 1
  · exact h1 d hd
  · exact h2 d (by omega)

end OMA.R_Erdos559_erdos_559_variants_trees_R1
