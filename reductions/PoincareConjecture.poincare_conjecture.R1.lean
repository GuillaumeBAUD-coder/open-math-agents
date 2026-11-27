import FormalConjectures.Millennium.Poincare
import Mathlib

/-!
A spherical covering becomes a homeomorphism over a simply connected base.
Apply this to elliptization after recovering compactness and simple connectivity
from a homotopy equivalence to the three-sphere. The elliptization input also
applies to closed manifolds with nontrivial finite fundamental group.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1

open scoped ContinuousMap Manifold
open ContinuousMap

/-- A homotopy three-sphere is closed. Noncompact connected manifolds have
vanishing top-dimensional ordinary homology with mod-two coefficients. -/
def H1 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M],
    (M ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) → CompactSpace M

/-- The fundamental group of the three-sphere is trivial. -/
def H2 : Prop := SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

/-- Spherical elliptization in covering-space form. -/
def H3 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M], (∀ x : M, Finite (FundamentalGroup M x)) →
    ∃ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M, IsCoveringMap p

theorem homeomorph_of_cover {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [ConnectedSpace E] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {p : E → X} (hp : IsCoveringMap p) : Nonempty (X ≃ₜ E) := by
  classical
  let e : E := Classical.ofNonempty
  obtain ⟨s,⟨hb,hs⟩,_⟩ := hp.existsUnique_continuousMap_lifts (ContinuousMap.id X) (p e) e rfl
  have right (x : X) : p (s x) = x := congrFun hs x
  have left : (s : X → E) ∘ p = id :=
    hp.eq_of_comp_eq (s.continuous.comp hp.continuous) continuous_id
      (funext fun u => right (p u)) e hb
  exact ⟨{ toFun := s
           invFun := p
           left_inv := right
           right_inv := fun u => congrFun left u
           continuous_toFun := s.continuous
           continuous_invFun := hp.continuous }⟩

theorem main : H1 → H2 → H3 → type_of% @PoincareConjecture.poincare_conjecture := by
  intro hcompact hsphere hell M _ _ _ e
  haveI : CompactSpace M := hcompact M e
  haveI : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := hsphere
  haveI : SimplyConnectedSpace M := e.simplyConnectedSpace
  haveI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace
    (EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨p,hp⟩ := hell M (fun _ => inferInstance)
  exact homeomorph_of_cover hp

end OMA.R_PoincareConjecture_poincare_conjecture_R1
