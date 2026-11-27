import Mathlib

/-!
# Coloring the odd distance graph

Source: https://www.openproblemgarden.org/op/coloring_the_odd_distance_graph
Published proof: James Davies, https://doi.org/10.1007/s00039-024-00659-w
Credit: @menelikbaye-digitalmethod
-/

namespace OMA.S_opg_coloring_the_odd_distance_graph

theorem main :
    ∀ (k : ℕ) (color : EuclideanSpace ℝ (Fin 2) → Fin k),
      ∃ x y : EuclideanSpace ℝ (Fin 2),
        x ≠ y ∧ color x = color y ∧ ∃ n : ℕ, Odd n ∧ dist x y = (n : ℝ) := by
  sorry

end OMA.S_opg_coloring_the_odd_distance_graph
