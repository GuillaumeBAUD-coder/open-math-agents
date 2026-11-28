import Mathlib

/-!
# Endpoint distance for an average-curvature-constrained planar path

Source: https://mathoverflow.net/questions/337612/lower-bound-of-the-distance-between-the-endpoints-of-an-average-curvature-constr
Credit: @chabodmasere

The continuous velocity is a derivative relative to the path's parameter
interval, including at its endpoints. Unit speed expresses parametrization by
arc length. The curvature hypothesis uses the ordinary unsigned angle between
the two velocity vectors, with the strict separation cutoff from the source.
-/

namespace OMA.S_mo_337612

abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem main :
    ∀ (L : ℝ), 0 ≤ L → L ≤ 2 * Real.pi →
    ∀ (γ v : ℝ → Plane),
      ContinuousOn v (Set.Icc 0 L) →
      (∀ t ∈ Set.Icc 0 L, HasDerivWithinAt γ (v t) (Set.Icc 0 L) t ∧ ‖v t‖ = 1) →
      (∀ t ∈ Set.Icc 0 L, ∀ s ∈ Set.Icc 0 L, t < s → s < t + Real.pi →
        InnerProductGeometry.angle (v t) (v s) ≤ s - t) →
      2 * Real.sin (L / 2) ≤ dist (γ L) (γ 0) := by
  sorry

end OMA.S_mo_337612
