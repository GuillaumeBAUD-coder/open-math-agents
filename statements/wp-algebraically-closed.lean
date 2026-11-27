import Mathlib

/-! Podewski's conjecture in characteristic zero. Definability allows parameters
from the field and refers to the standard ring operations.
Source: Wikipedia, List of unsolved problems in mathematics, Model theory.
-/

namespace OMA.S_wp_algebraically_closed

theorem main :
    ∀ (K : Type*) [Field K] [Infinite K] [CharZero K],
      letI := FirstOrder.Ring.compatibleRingOfRing K
      (∀ s : Set K, (Set.univ : Set K).Definable₁ FirstOrder.Language.ring s →
        s.Finite ∨ sᶜ.Finite) → IsAlgClosed K := by
  sorry

end OMA.S_wp_algebraically_closed
