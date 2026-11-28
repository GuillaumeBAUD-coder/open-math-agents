import Mathlib

/-!
# Coloring random subgraphs

Sources
- https://www.openproblemgarden.org/op/coloring_random_subgraphs
- https://www.borisbukh.org/problems.html

The logarithmic ratio is stated for chromatic numbers at least two.
-/

namespace OMA.S_opg_coloring_random_subgraphs

universe u

/-- Independent retention with probability one half gives the uniform distribution on
subsets of the original edge set. The spanning subgraph retains the same vertex type. -/
noncomputable def expectedChromaticNumber {V : Type u} [Fintype V]
    (G : SimpleGraph V) : ℝ := by
  classical
  exact (∑ edges ∈ G.edgeFinset.powerset,
      ((SimpleGraph.fromEdgeSet (edges : Set (Sym2 V))).chromaticNumber.toNat : ℝ)) /
    (2 : ℝ) ^ G.edgeFinset.card

theorem main : ∃ c : ℝ, 0 < c ∧
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
      let k := G.chromaticNumber.toNat
      2 ≤ k → c * ((k : ℝ) / Real.log (k : ℝ)) < expectedChromaticNumber G := by
  sorry

end OMA.S_opg_coloring_random_subgraphs
