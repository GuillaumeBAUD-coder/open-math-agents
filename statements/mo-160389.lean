import Mathlib

/-!
# MathOverflow 160389

Source: https://mathoverflow.net/questions/160389
-/

namespace OMA.S_mo_160389

open Finset

def Representable (a : Fin 3 → ℕ) (k : ℕ) : Prop :=
  ∃ w : Equiv.Perm (Fin 3) → ℕ, ∀ i, ∑ σ, w σ * a (σ i) = k

theorem main : ∀ a : Fin 3 → ℕ, (∀ i, 0 < a i) →
      Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → Odd (∑ i, a i) →
      ∃ k : ℕ, ¬ Representable a k ∧ ∀ j, ¬ Representable a j → j ≤ k := by
  sorry

end OMA.S_mo_160389
