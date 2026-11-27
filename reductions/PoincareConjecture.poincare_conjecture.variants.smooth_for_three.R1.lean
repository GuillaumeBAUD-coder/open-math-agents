import FormalConjectures.Millennium.Poincare

/-!
Credit: @willspag

Topological recognition and uniqueness of smoothing give two independent
ways to share work on the smooth three-sphere. For the topological step,
the spherical-covering formulation of elliptization is one route. For the
second step, a homeomorphism supplies the compactness of its source, and
compact locally Euclidean spaces are second countable. The smoothing step
asserts the existence of a diffeomorphism, which can differ from the
homeomorphism supplied by the first step.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_for_three_R1

open scoped Manifold ContDiff EuclideanGeometry ContinuousMap

universe u

def H1 : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M],
    (M ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) →
      Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

def H2 : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [SecondCountableTopology M],
    (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) →
      Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

lemma smooth_sphere_of_topological_recognition : H1.{u} → H2.{u} →
    type_of% @PoincareConjecture.poincare_conjecture.variants.smooth_for_three.{u} := by
  intro recognize smooth M _ _ _ _ h
  obtain ⟨e⟩ := recognize M h
  letI : CompactSpace M := Function.Surjective.compactSpace e.symm.continuous e.symm.surjective
  letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact (ℝ^3) M
  exact smooth M e

theorem main : H1 → H2 → type_of% @PoincareConjecture.poincare_conjecture.variants.smooth_for_three := by
  exact smooth_sphere_of_topological_recognition

end OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_for_three_R1
