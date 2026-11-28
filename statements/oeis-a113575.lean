import Mathlib

/-!
# A113575: a palindromic prime of 2n - 1 digits congruent to 1 modulo n

Source: https://oeis.org/A113575
Credit: @R-Dson

`a(n)` is the least palindromic prime with exactly `2n - 1` digits that is congruent to `1`
modulo `n`, or `0` if no such prime exists. Conjecture: no term is zero.

Conventions.
- A palindrome is a number whose decimal digits read the same backwards, and a number with
  `2n - 1` digits is one with exactly `2n - 1` decimal digits.
- Congruent to `1` modulo `n` means `n ∣ p - 1`. (For `n = 1` this holds for every prime, which
  is why `a(1) = 2`.)
- `a(n)` is the infimum in `ℕ` of the set of such primes, so it is `0` exactly when the set is
  empty.
- The offset of the entry is `1`.
- First terms of the entry: 2, 101, 10501, 1003001, 100030001, ...
-/

namespace OMA.S_oeis_a113575

/-- Least palindromic prime with exactly `2 * n - 1` decimal digits and congruent to `1` modulo
`n`, or `0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ (Nat.digits 10 p).Palindrome ∧ (Nat.digits 10 p).length = 2 * n - 1 ∧
    n ∣ p - 1}

theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a113575
