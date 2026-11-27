import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.KrullDimension

/-!
# Torsion conjecture

Source: https://en.wikipedia.org/wiki/Torsion_conjecture
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_torsion_conjecture

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped MonObj

/-- An abelian variety over a field, represented as a proper geometrically integral group scheme. -/
structure AbelianVariety (K : Type u) [Field K] where
  schemeOver : Over (Spec (.of K))
  proper : IsProper schemeOver.hom
  geometricallyIntegral : GeometricallyIntegral schemeOver.hom
  groupObject : GrpObj schemeOver

/-- The dimension of the underlying scheme of an abelian variety. -/
noncomputable def dimension (K : Type u) [Field K] (A : AbelianVariety K) : WithBot ℕ∞ :=
  topologicalKrullDim A.schemeOver.left

/-- The extended natural cardinality of the finite-order rational points of an abelian variety. -/
noncomputable def rationalTorsionCard (K : Type u) [Field K] (A : AbelianVariety K) : ℕ∞ :=
  letI := A.groupObject
  ENat.card {x : 𝟙_ (Over (Spec (.of K))) ⟶ A.schemeOver // IsOfFinOrder x}

theorem main :
    ∀ (K : Type u) [Field K] [NumberField K] (g : ℕ),
      ∃ B : ℕ,
        ∀ A : AbelianVariety K,
          dimension K A = g → rationalTorsionCard K A ≤ (B : ℕ∞) := by
  sorry

end OMA.S_wp_torsion_conjecture
