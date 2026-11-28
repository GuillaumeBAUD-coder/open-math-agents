import Mathlib

/-!
# A005385: conjectures on safe primes

Source: https://oeis.org/A005385
Credit: @jagraj28

A005385 lists the safe primes: primes `p` such that `(p - 1)/2` is also prime
(5, 7, 11, 23, 47, ...). The entry records:
1. (Vladimir Shevelev, 2015) a strengthening of Bertrand's postulate: for `n ≥ 24`, the interval
   `(n, 2n)` contains a safe prime;
2. (M. F. Hasler, 2021) there are infinitely many safe primes, and their estimated asymptotic
   density `~ 2C/(log n)^2`, with `C` the twin prime constant, converges to the actual value.

`main` is the conjunction of conjecture 1 and the first claim of conjecture 2 (infinitely many
safe primes).

Choices:
* Interval `(n, 2n)` is read as open: `n < p < 2n`.
* `(p - 1)/2` is natural-number division; for an odd prime `p` it is exact, and for `p = 2` it
  is `0`, which is not prime, so 2 is not a safe prime, as in the sequence.
* The density claim of conjecture 2 is left out. It is phrased as an estimate (it converges as
  far as we know), and its normalisation is unclear: the Bateman–Horn heuristic gives
  `#{safe p ≤ x} ~ C x/(log x)^2`, a density of `C/(log n)^2` among all integers (or `2C/(log n)^2`
  among odd integers only), and a count to `10^7` (30657 safe primes, against about 25400 for
  `C x/(log x)^2` and 50800 for `2C x/(log x)^2`) agrees with the former. Fixing one reading
  would be a guess at the author's meaning.
-/

namespace OMA.S_oeis_a005385

/-- `p` is a safe prime (OEIS A005385): `p` and `(p - 1)/2` are both prime. -/
def IsSafePrime (p : ℕ) : Prop := p.Prime ∧ ((p - 1) / 2).Prime

/-- Shevelev's conjecture and the infinitude of safe primes (OEIS A005385). -/
theorem main :
    (∀ n : ℕ, 24 ≤ n → ∃ p : ℕ, IsSafePrime p ∧ n < p ∧ p < 2 * n) ∧
    {p : ℕ | IsSafePrime p}.Infinite := by
  sorry

end OMA.S_oeis_a005385
