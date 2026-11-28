import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Set.Finite.Basic

/-!
# OEIS A205510

The conjecture is that infinitely many pairs of consecutive primes differ
in exactly one binary digit. The binary digit sum of the bitwise XOR counts
positions that differ, including when the two primes have different bit lengths.
Source: https://oeis.org/A205510
-/

namespace OMA.S_oeis_a205510

def binaryHammingDistance (p q : ℕ) : ℕ := (Nat.digits 2 (p ^^^ q)).sum

theorem main :
    {n : ℕ | binaryHammingDistance (Nat.nth Nat.Prime n)
      (Nat.nth Nat.Prime (n + 1)) = 1}.Infinite := by
  sorry

end OMA.S_oeis_a205510
