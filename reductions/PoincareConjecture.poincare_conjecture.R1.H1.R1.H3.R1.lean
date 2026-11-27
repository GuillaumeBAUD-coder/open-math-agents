import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R1
open CategoryTheory AlgebraicTopology

/-- The universal cover of the plane unit circle has infinite cyclic deck group. -/
def H1 : Prop :=
  PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
    ∃ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, Nonempty (FundamentalGroup _ x ≃* Multiplicative ℤ)

/-- Degree-one Hurewicz in the infinite cyclic case. -/
def H2 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [PathConnectedSpace X] (x : X),
    Nonempty (FundamentalGroup X x ≃* Multiplicative ℤ) →
    Nonempty (((singularHomologyFunctor AddCommGrpCat 1).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of X) ≅ AddCommGrpCat.of ℤ)

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1.H3 := by
  rintro ⟨hc,x,hx⟩ hur
  letI := hc
  exact hur _ x hx

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R1
