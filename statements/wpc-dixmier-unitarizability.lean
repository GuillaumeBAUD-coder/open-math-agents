import Mathlib

/-!
Dixmier’s problem for discrete groups, without a countability assumption.
Source: https://en.wikipedia.org/wiki/Uniformly_bounded_representation
Definitions adapted from OpenAI, openai/math (Apache-2.0), commit
3344da59991ed94f9ba711217b29c1d760badfa6, ComparatorChallenges/DixmierAllDiscrete.lean.
A conjugated group representation already acts by invertible maps, so norm
preservation expresses unitarity. Only the converse asked for is stated.
-/
namespace OMA.S_wpc_dixmier_unitarizability
noncomputable section
universe u v
open scoped BoundedContinuousFunction

def leftTranslate {G : Type u} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (g : G) (f : G →ᵇ ℂ) : G →ᵇ ℂ :=
  f.compContinuous ⟨fun x => g⁻¹ * x, continuous_of_discreteTopology⟩

def Amenable (G : Type u) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] : Prop :=
  ∃ m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ,
    m (BoundedContinuousFunction.const G 1) = 1 ∧
    (∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) ∧
    ∀ (g : G) (f : G →ᵇ ℂ), m (leftTranslate g f) = m f

def SimilarToUnitary {G : Type u} [Group G]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)) : Prop :=
  ∃ S : H ≃L[ℂ] H, ∀ (g : G) (x : H), ‖S (π g (S.symm x))‖ = ‖x‖

def Unitarizable (G : Type u) [Group G] : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : G →* (H →L[ℂ] H)),
    (∃ C : ℝ, ∀ g, ‖π g‖ ≤ C) → SimilarToUnitary π

theorem main :
    ∀ (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G],
      Unitarizable.{u, max u v} G → Amenable G := by
  sorry

end
end OMA.S_wpc_dixmier_unitarizability
