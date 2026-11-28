import Mathlib

/-!
# A111252: primes `p` such that the gap between the closest surrounding squares is prime.

Source: https://oeis.org/A111252
Credit: @cjchaffin

For a prime `p`, the closest squares surrounding `p` are the unique pair `k^2 < p < (k+1)^2`.
The example is `p = 29`, with `5^2` and `6^2`, and `36 - 25 = 11` prime.

Conjecture (on the OEIS page): the number of terms is infinite.
-/

namespace OMA.S_oeis_a111252

def SurroundingSquareGapPrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ k : ℕ, k ^ 2 < p ∧ p < (k + 1) ^ 2 ∧ ((k + 1) ^ 2 - k ^ 2).Prime

theorem main : {p : ℕ | SurroundingSquareGapPrime p}.Infinite := by
  sorry

end OMA.S_oeis_a111252
