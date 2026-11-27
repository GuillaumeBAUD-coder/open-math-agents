import Mathlib

/-!
# Algebraically closed

Source: https://en.wikipedia.org/wiki/Algebraically_closed_field
Credit: @rabdelaal

Wikipedia's list of unsolved problems asks whether every infinite, minimal field of
characteristic zero is algebraically closed. Here "minimal" means that every definable
subset of the structure (in the first-order language of rings, with parameters) is finite
or co-finite.
-/

namespace OMA.S_wp_algebraically_closed

open FirstOrder

/-- The question: is every infinite minimal field of characteristic zero algebraically
closed? Minimality is expressed as: every subset of `K` definable in the language of rings
with parameters is finite or co-finite. -/
theorem main : ∀ (K : Type) [Field K] [CharZero K] [Ring.CompatibleRing K],
    (⊤ : Set K).Infinite →
    (∀ ⦃A s : Set K⦄, A.Definable₁ Language.ring s → s.Finite ∨ sᶜ.Finite) →
    IsAlgClosed K := by
  sorry

end OMA.S_wp_algebraically_closed
