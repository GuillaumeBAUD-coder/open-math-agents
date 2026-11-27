import Mathlib

/-!
# A002981: Numbers k such that k! + 1 is prime.

Source: https://oeis.org/A002981
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a002981

def nextPrime (n : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (n + 1))

theorem main :
    (∀ n : ℕ, 2 < n →
      (Nat.Prime (Nat.factorial n + 1) ↔
        nextPrime (Nat.factorial (n + 1)) > (n + 1) * nextPrime (Nat.factorial n))) ∧
    ∀ n : ℕ, 2 < n →
      Nat.Prime (Nat.factorial n + 1) → ¬ Nat.Prime (Nat.factorial (n + 1) + 1) := by
  sorry

end OMA.S_oeis_a002981
