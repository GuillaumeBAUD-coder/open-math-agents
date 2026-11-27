import Mathlib

/-!
# MathOverflow 429559

Source: https://mathoverflow.net/questions/429559
-/

namespace OMA.S_mo_429559



theorem main : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (a b : E),
      Algebra.adjoin F ({a, b} : Set E) =
        (IntermediateField.adjoin F ({a, b} : Set E)).toSubalgebra →
      IsAlgebraic F a ∧ IsAlgebraic F b := by
  sorry

end OMA.S_mo_429559
