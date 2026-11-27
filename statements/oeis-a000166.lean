import Mathlib

/-!
# A000166: Subfactorial or rencontres numbers, or derangements: number of permutations of n elements with no fixed points.

Source: https://oeis.org/A000166
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a000166

def derangementCount (n : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin n) // ∀ i, σ i ≠ i}

def IsPerfectPower (m : ℕ) : Prop :=
  ∃ x k : ℕ, 1 < x ∧ 1 < k ∧ m = x ^ k

theorem main : ∀ n : ℕ, 2 < n →
    (IsPerfectPower (derangementCount n) ↔ n = 4) := by
  sorry

end OMA.S_oeis_a000166
