import Mathlib

namespace OMA.S_mo_259117

/-- Can nonisomorphic torsion-free abelian groups have isomorphic fraction fields
of their rational group algebras? -/
theorem main :
    ∃ (G H : Type) (groupG : CommGroup G) (groupH : CommGroup H),
      letI : CommGroup G := groupG
      letI : CommGroup H := groupH
      IsMulTorsionFree G ∧ IsMulTorsionFree H ∧
      (¬ Nonempty (G ≃* H)) ∧
      Nonempty
        (FractionRing (MonoidAlgebra ℚ G) ≃+* FractionRing (MonoidAlgebra ℚ H)) := by
  sorry

end OMA.S_mo_259117
