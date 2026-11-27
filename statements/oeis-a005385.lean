import Mathlib

/-!
# OEIS A005385: safe primes, and a strengthening of Bertrand's postulate

Credit: @ajs808

A safe prime is a prime `p` such that `(p - 1) / 2` is also prime
(5, 7, 11, 23, 47, 59, 83, ...).

Conjecture (Vladimir Shevelev, Jul 06 2015), stated in the comments of https://oeis.org/A005385 :
there is a strengthening of the Bertrand postulate for `n ≥ 24`: the interval `(n, 2 n)` contains
a safe prime. (Tested by Peter J. C. Moses up to `n = 10^7`.)

The interval is open, as in the source. The bound `24` is sharp: for `n = 23` the open interval
`(23, 46)` contains no safe prime (the next one after 23 is 47).

Only this conjecture is stated here. The same entry also mentions the conjecture that there are
infinitely many safe primes (with an asymptotic density estimate), which this statement implies
but which is not formalized separately in this file.

*References:*
- [A005385](https://oeis.org/A005385)
-/

namespace OMA.S_oeis_a005385

/-- `p` is a safe prime: `p` is prime and `(p - 1) / 2` is prime.
For an odd prime `p` the division is exact; for `p = 2` it gives `0`, which is not prime. -/
def IsSafePrime (p : ℕ) : Prop := p.Prime ∧ ((p - 1) / 2).Prime

/-- Conjecture (OEIS A005385, V. Shevelev): for every `n ≥ 24` there is a safe prime `p`
with `n < p < 2 n`. -/
theorem main : ∀ n : ℕ, 24 ≤ n → ∃ p : ℕ, n < p ∧ p < 2 * n ∧ IsSafePrime p := by
  sorry

end OMA.S_oeis_a005385
