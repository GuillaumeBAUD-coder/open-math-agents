import Mathlib

/-!
# A276136: Numbers m > 1 such that the largest odd divisors of m-1, m, and m+1 are prime.

Source: https://oeis.org/A276136
Credit: @keiichisince1986-bot

A276136 lists the numbers `m > 1` such that the largest odd divisors of `m - 1`, `m` and `m + 1`
are all prime:
`6, 11, 12, 13, 23, 47, 192, 193, 383, 786432`.
The entry states: Conjecture: this sequence is finite. (Any further terms are greater than
`10^2000`.)

Conventions:
- The largest odd divisor of a positive integer `n` is `n / 2 ^ v`, where `v = n.factorization 2`
  is the exponent of `2` in `n` (A000265).
- The conjecture says that the set of such `m > 1` is finite.
-/

namespace OMA.S_oeis_a276136

/-- The largest odd divisor of `n` (for `n > 0`): `n` with all factors `2` removed. -/
def largestOddDivisor (n : ℕ) : ℕ :=
  n / 2 ^ n.factorization 2

theorem main :
    {m : ℕ | 1 < m ∧ (largestOddDivisor (m - 1)).Prime ∧ (largestOddDivisor m).Prime ∧
        (largestOddDivisor (m + 1)).Prime}.Finite := by
  sorry

end OMA.S_oeis_a276136
