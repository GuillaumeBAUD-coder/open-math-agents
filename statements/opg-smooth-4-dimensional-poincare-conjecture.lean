import Mathlib

/-! # Smooth four-dimensional Poincaré conjecture

A smooth four-manifold having the homotopy type of the standard four-sphere
is conjectured to be diffeomorphic to it. The sphere is the unit sphere in
real five-space, equipped with its standard smooth structure.

Source: https://www.openproblemgarden.org/op/smooth_4_dimensional_poincare_conjecture
See also the corpus entry PoincareConjecture.poincare_conjecture.variants.smooth_dimension_four.
Credit: @steveDOTdigital
-/

namespace OMA.S_opg_smooth_4_dimensional_poincare_conjecture

open scoped Manifold ContDiff ContinuousMap

universe u

abbrev FourSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1

theorem main : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M],
    M ≃ₕ FourSphere → Nonempty (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ FourSphere) := by
  sorry

end OMA.S_opg_smooth_4_dimensional_poincare_conjecture
