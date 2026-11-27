import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1
open AlgebraicTopology CategoryTheory

/-- Stereographic charts cover the sphere, with a cylindrical overlap. -/
def H1 : Prop :=
  ∃ U V : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1), IsOpen U ∧ IsOpen V ∧ U ∪ V = Set.univ ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧ Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
      Nonempty (↥(U ∩ V) ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Ioi (0 : ℝ)))

/-- Mayer–Vietoris for two Euclidean charts with cylindrical intersection. -/
def H2 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (U V : Set X),
    (IsOpen U ∧ IsOpen V ∧ U ∪ V = Set.univ ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧ Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
      Nonempty (↥(U ∩ V) ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Ioi (0 : ℝ)))) →
    Nonempty (((singularHomologyFunctor AddCommGrpCat 3).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X) ≅
      ((singularHomologyFunctor AddCommGrpCat 2).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)))

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1.H1 := by
  rintro ⟨U,V,h⟩ hMV
  exact hMV _ U V h

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1
