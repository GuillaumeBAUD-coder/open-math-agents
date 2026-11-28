import Mathlib

/-!
# A111441: Numbers k such that the sum of the squares of the first k primes is divisible by k.

Source: https://oeis.org/A111441
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a111441

noncomputable def sumSquaresFirstPrimes (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, Nat.nth Nat.Prime i ^ 2

def IsTerm (k : ℕ) : Prop :=
  0 < k ∧ k ∣ sumSquaresFirstPrimes k

theorem main : ∀ k : ℕ, IsTerm k → k % 12 ≠ 3 ∧ k % 12 ≠ 9 := by
  sorry

end OMA.S_oeis_a111441
