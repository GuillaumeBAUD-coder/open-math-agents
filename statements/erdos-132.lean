import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Prod

/-!
# Distances of small positive multiplicity in a finite planar set

Erdős and Pach asked for two such distances and for a number growing without bound.
The finite conjecture is stated from five points onward in Erdős Problem 132.
Source: https://www.erdosproblems.com/132. Formalization by @saientropy.
-/

namespace OMA.S_erdos_132

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The number of unordered pairs of distinct points at distance `d`. Each unordered
pair occurs in both orders in `A.offDiag`. -/
noncomputable def multiplicity (A : Finset Plane) (d : ℝ) : ℕ := by
  classical
  exact (A.offDiag.filter (fun pair => dist pair.1 pair.2 = d)).card / 2

/-- The distances that occur at least once and at most as many times as there are points. -/
noncomputable def rareDistances (A : Finset Plane) : Finset ℝ := by
  classical
  exact (A.offDiag.image (fun pair => dist pair.1 pair.2)).filter
    (fun d => multiplicity A d ≤ A.card)

/-- Every planar set of at least five points has at least two distances of multiplicity
between one and its cardinality. For every desired number of such distances, all
sufficiently large finite planar sets have at least that many. -/
theorem main :
    (∀ A : Finset Plane, 5 ≤ A.card → 2 ≤ (rareDistances A).card) ∧
      ∀ B : ℕ, ∃ N : ℕ, ∀ A : Finset Plane, N ≤ A.card → B ≤ (rareDistances A).card := by
  sorry

end OMA.S_erdos_132
