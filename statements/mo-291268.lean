import Mathlib

namespace OMA.S_mo_291268

open Classical in
/-- Is there one infinite algebraic extension of the rationals over which
every elliptic curve has a finitely generated group of rational points? -/
theorem main :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K),
      Algebra.IsAlgebraic ℚ K ∧ ¬ FiniteDimensional ℚ K ∧
      ∀ (E : WeierstrassCurve K) [E.IsElliptic], AddGroup.FG E.toAffine.Point := by
  sorry

end OMA.S_mo_291268
