import Mathlib.Data.Nat.Prime.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Prime sums from permutations of the first n positive integers

Zhi-Wei Sun formulated two conjectures for OEIS A321610. The entry also records
Max Alekseyev's perfect-matching argument for the square-count assertion.
The index i : Fin n represents the positive integer i.val + 1.

Source: https://oeis.org/A321610
Credit: @hiattco
-/

namespace OMA.S_oeis_a321610

/-- The number of permutations for which every sum of two squares is prime. -/
noncomputable def primePermutationCount (n : ℕ) : ℕ :=
  Nat.card {σ : Equiv.Perm (Fin n) //
    ∀ i : Fin n, Nat.Prime ((i.val + 1)^2 + ((σ i).val + 1)^2)}

theorem main :
    ∀ n : ℕ, 0 < n →
      IsSquare (primePermutationCount n) ∧
      (primePermutationCount n = 0 ↔ n = 7) ∧
      ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n,
        let x := i.val + 1
        let y := (σ i).val + 1
        Nat.Prime (x^2 + x*y + y^2) := by
  sorry

end OMA.S_oeis_a321610
