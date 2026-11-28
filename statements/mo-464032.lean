import Mathlib

/-!
# MathOverflow 464032

Source: https://mathoverflow.net/questions/464032
-/

namespace OMA.S_mo_464032

open Finset

def inversionCount {n : ℕ} (σ : Equiv.Perm (Fin (2 * n + 1))) (sameParity : Bool) : ℕ :=
  (univ.filter fun ij : Fin (2 * n + 1) × Fin (2 * n + 1) =>
    ij.1 < ij.2 ∧ σ ij.2 < σ ij.1 ∧
      decide (ij.1.val % 2 = ij.2.val % 2) = sameParity).card

theorem main : ∀ n : ℕ, ∀ σ : Equiv.Perm (Fin (2 * n + 1)),
    (∀ i, (σ i).val % 2 = i.val % 2) → inversionCount σ true ≤ inversionCount σ false := by
  sorry

end OMA.S_mo_464032
