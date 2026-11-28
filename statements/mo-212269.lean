import Mathlib

namespace OMA.S_mo_212269

open scoped Manifold ContDiff
open Set

abbrev Ambient := EuclideanSpace ℝ (Fin 4)
abbrev ThreeSphere := Metric.sphere (0 : Ambient) 1
abbrev AmbientBilinear := Ambient →L[ℝ] Ambient →L[ℝ] ℝ

/-- The standard unknot is the equatorial circle in the first two coordinates. -/
def equator : Set ThreeSphere :=
  {x | (x : Ambient) 2 = 0 ∧ (x : Ambient) 3 = 0}

/-- Twice the energy of a period-one loop for the restricted ambient metric. -/
noncomputable def loopEnergy (g : ThreeSphere → AmbientBilinear)
    (γ : ℝ → ThreeSphere) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    g (γ t) (deriv (fun u => (γ u : Ambient)) t)
      (deriv (fun u => (γ u : Ambient)) t)

/-- A loop is stationary for energy under every smooth periodic variation. -/
def stationary (g : ThreeSphere → AmbientBilinear) (γ : ℝ → ThreeSphere) : Prop :=
  ∀ F : ℝ × ℝ → ThreeSphere,
    ContMDiff (𝓘(ℝ, ℝ × ℝ)) (𝓡 3) ∞ F →
    (∀ s, Function.Periodic (fun t => F (s, t)) 1) →
    (∀ t, F (0, t) = γ t) →
    HasDerivAt (fun s => loopEnergy g (fun t => F (s, t))) 0 0

/-- Is there a smooth Riemannian metric on the three-sphere for which every
simple closed geodesic is topologically knotted? -/
theorem main :
    ∃ g : ThreeSphere → AmbientBilinear,
      ContMDiff (𝓡 3) (𝓘(ℝ, AmbientBilinear)) ∞ g ∧
      (∀ x u v, g x u v = g x v u) ∧
      (∀ x u, u ≠ 0 → 0 < g x u u) ∧
      ∀ γ : ℝ → ThreeSphere,
        ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ γ →
        Function.Periodic γ 1 →
        InjOn γ (Ico 0 1) →
        (∀ t, deriv (fun u => (γ u : Ambient)) t ≠ 0) →
        stationary g γ →
        ¬ ∃ h : ThreeSphere ≃ₜ ThreeSphere, h '' range γ = equator := by
  sorry

end OMA.S_mo_212269
