import Mathlib

/-!
# MathOverflow 185536

Source: https://mathoverflow.net/questions/185536
-/

namespace OMA.S_mo_185536



theorem main : ∀ (A : Type) [CStarAlgebra A] (a b : A),
    IsSelfAdjoint a → IsSelfAdjoint b → a ≠ b → NormedSpace.exp a ≠ NormedSpace.exp b := by
  sorry

end OMA.S_mo_185536
