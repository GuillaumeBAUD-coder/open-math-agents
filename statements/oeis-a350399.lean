import Mathlib

/-!
# A350399: a(n) is the number of prime pairs (p, q) with p <= q, p + q = 2*n, and p*q mod (2*n) prime

Source: https://oeis.org/A350399
Credit: @ceejcake

OEIS A350399 (offset 1) counts pairs of primes `(p, q)` with `p ≤ q`, `p + q = 2 * n`,
and `(p * q) mod (2 * n)` prime (taking the standard remainder in `{0, ..., 2 * n - 1}`).
Since `p` is prime and `p ≤ q = 2 * n - p`, this is in bijection with
`p ∈ Finset.Icc 2 n` such that `p`, `2 * n - p`, and `(p * (2 * n - p)) % (2 * n)` are prime
(with no underflow since `p ≤ n`).

Initial values: `a(1)..a(20) = 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 2, 3, 2, 1, 3, 1, 2`.

Conjecture (J. M. Bergot and Robert Israel, OEIS A350399):
For all `n ≥ 3`, `a(n) > 0`.
-/

namespace OMA.S_oeis_a350399

/-- The sequence OEIS A350399 (offset 1): the number of prime pairs `(p, q)` with `p ≤ q`,
`p + q = 2 * n`, and `(p * q) mod (2 * n)` prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 2 n).filter fun p =>
    p.Prime ∧ (2 * n - p).Prime ∧ (p * (2 * n - p) % (2 * n)).Prime).card

/-- Conjecture (OEIS A350399): for all `n ≥ 3`, `a(n) > 0`. -/
theorem main : ∀ n : ℕ, 3 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a350399
