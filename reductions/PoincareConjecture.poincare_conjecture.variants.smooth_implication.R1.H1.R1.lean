import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_smooth_implication_R1
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.Grp.Abelian

-- Reduction PoincareConjecture.poincare_conjecture.variants.smooth_implication.R1.H1.R1 of step PoincareConjecture.poincare_conjecture.variants.smooth_implication.R1.H1
-- Credit: @marcusbuffett

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_implication_R1_H1_R1

open AlgebraicTopology CategoryTheory Limits
open scoped ContinuousMap EuclideanGeometry

-- Homology transport adapted from @tamoghnokandar.
private theorem homotopy_homology_iso (n : ℕ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) :
    Nonempty ((((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)) ≅
      (((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of Y))) := by
  let F := (singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  refine ⟨⟨F.map f, F.map g, ?_, ?_⟩⟩
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨h⟩ := e.left_inv
    have hh : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) := h
    exact hh.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨h⟩ := e.right_inv
    have hh : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of Y)) := h
    exact hh.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n

def H1 : Prop :=
  ¬ IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj (AddCommGrpCat.of ℤ)).obj
    (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)))

def H2 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M]
    [ConnectedSpace M], ¬ CompactSpace M →
    IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of M))

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_implication_R1.H1 := by
  intro sphereH vanishes M _ _ _ e
  classical
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
  letI : PathConnectedSpace S := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      norm_num) _ zero_le_one)
  obtain ⟨h⟩ := e.left_inv
  letI : PathConnectedSpace M :=
    ⟨⟨e.invFun (Classical.choice (inferInstance : Nonempty S))⟩, fun x y =>
      ((show Joined (e.invFun (e x)) x from ⟨h.evalAt x⟩).symm.trans
        ((PathConnectedSpace.joined (e x : S) (e y)).map e.invFun.continuous)).trans
        (show Joined (e.invFun (e y)) y from ⟨h.evalAt y⟩)⟩
  by_contra hnc
  obtain ⟨i⟩ := homotopy_homology_iso 3 e
  exact sphereH ((vanishes M hnc).of_iso i.symm)

end OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_implication_R1_H1_R1
