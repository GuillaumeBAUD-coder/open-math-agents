import Mathlib

/-!
# Algebraically closed

Source: https://en.wikipedia.org/wiki/algebraically_closed_field
Credit: @gunnerhowe

Open problem from the source: is every infinite, minimal field of characteristic zero
algebraically closed? Here a field is minimal when every definable subset of the structure is
finite or co-finite. (This is Podewski's conjecture; Wagner proved it in positive characteristic.)

Reading of the source, as is standard in model theory:
* the field is a structure in the first-order language of rings, `FirstOrder.Language.ring`,
  interpreted by its own `+`, `*`, `-`, `0`, `1` (`FirstOrder.Ring.compatibleRingOfRing`);
* definable means definable with parameters from the field (parameter set `Set.univ`), and the
  subsets in question are subsets of the field itself (one free variable);
* the question is stated in its conjectured positive form.
-/

namespace OMA.S_wp_algebraically_closed

open FirstOrder FirstOrder.Language

universe u

/-- A field `K` is minimal if every subset of `K` that is definable in the language of rings,
with parameters from `K`, is finite or co-finite. -/
def IsMinimalField (K : Type u) [Field K] : Prop :=
  letI := FirstOrder.Ring.compatibleRingOfRing K
  ∀ s : Set K, (Set.univ : Set K).Definable Language.ring {v : Fin 1 → K | v 0 ∈ s} →
    s.Finite ∨ sᶜ.Finite

/-- Every infinite minimal field of characteristic zero is algebraically closed. -/
theorem main : ∀ (K : Type u) [Field K], CharZero K → Infinite K → IsMinimalField K →
    IsAlgClosed K := by
  sorry

end OMA.S_wp_algebraically_closed
