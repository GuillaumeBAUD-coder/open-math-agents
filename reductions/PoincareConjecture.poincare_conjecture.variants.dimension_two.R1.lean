import FormalConjectures.Millennium.Poincare
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Homology and the classification of closed surfaces

A surface of the homotopy type of the two-sphere has nonzero second singular
homology. The top homology of a connected noncompact surface vanishes, so the
surface is compact. Simple connectedness then identifies it with the sphere
by the classification of compact surfaces. See Hatcher, Algebraic Topology,
Section 3.3, and https://github.com/mccorvie/classification-of-surfaces.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1

open AlgebraicTopology CategoryTheory Limits
open scoped ContinuousMap

private theorem homotopy_homology_iso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) :
    Nonempty ((((singularHomologyFunctor AddCommGrpCat 2).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)) ≅
      (((singularHomologyFunctor AddCommGrpCat 2).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of Y))) := by
  let F := (singularHomologyFunctor AddCommGrpCat 2).obj (AddCommGrpCat.of ℤ)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  refine ⟨⟨F.map f, F.map g, ?_, ?_⟩⟩
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨h⟩ := e.left_inv
    have hh : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) := h
    exact hh.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) 2
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨h⟩ := e.right_inv
    have hh : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of Y)) := h
    exact hh.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) 2

/-- The two-sphere has nonzero integral homology in degree two. -/
def H1 : Prop :=
  ¬ IsZero (((singularHomologyFunctor AddCommGrpCat 2).obj (AddCommGrpCat.of ℤ)).obj
    (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)))

/-- The top integral homology of a connected noncompact surface vanishes. -/
def H2 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [ConnectedSpace M], ¬ CompactSpace M →
    IsZero (((singularHomologyFunctor AddCommGrpCat 2).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of M))

/-- The two-sphere is simply connected. -/
def H3 : Prop :=
  SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

/-- The compact simply connected case of the classification of surfaces. -/
def H4 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

theorem main : H1 → H2 → H3 → H4 →
    type_of% @PoincareConjecture.poincare_conjecture.variants.dimension_two := by
  intro hSphere hVanishing hSC hClass M _ _ _ e
  have : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := hSC
  have : SimplyConnectedSpace M := e.simplyConnectedSpace
  have : CompactSpace M := by
    by_contra h
    have hZero := hVanishing M h
    obtain ⟨iso⟩ := homotopy_homology_iso e
    exact hSphere (hZero.of_iso iso.symm)
  exact hClass M

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1
