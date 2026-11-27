import Mathlib

/-!
# Torsion conjecture

Source: https://en.wikipedia.org/wiki/Torsion_conjecture
Credit: @Ciphore

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source states the conjecture for a fixed number field: the order of the torsion group is
bounded in terms of the dimension of the abelian variety and the number field.  We use a proper,
geometrically integral group scheme over the field as the abelian variety, and its sections over
the field as its rational points.  Finiteness is included explicitly because `Nat.card` is zero on
infinite types.
-/

namespace OMA.S_wp_torsion_conjecture

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj

/-- The uniform boundedness conjecture for torsion points on abelian varieties over a fixed
number field. -/
theorem main : ∀ (K : Type*) [Field K] [NumberField K] (g : ℕ), ∃ B : ℕ,
    ∀ (G : Over (Spec (.of K))) [GrpObj G] [IsProper G.hom] [GeometricallyIntegral G.hom],
      topologicalKrullDim G.left = g →
        Finite {x : 𝟙_ (Over (Spec (.of K))) ⟶ G // IsOfFinOrder x} ∧
        Nat.card {x : 𝟙_ (Over (Spec (.of K))) ⟶ G // IsOfFinOrder x} ≤ B := by
  sorry

end OMA.S_wp_torsion_conjecture
