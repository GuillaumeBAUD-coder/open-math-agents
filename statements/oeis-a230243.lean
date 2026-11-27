import Mathlib

/-!
# A230243: Number of primes p < n with 3*p + 8 and (p-1)*n + 1 both prime.

Source: https://oeis.org/A230243
Credit: @sntntHb

Conjecture (stated on the OEIS page, entry by Zhi-Wei Sun): `a(n) > 0` for all `n > 4`, i.e. for
every integer `n > 4` there is a prime `p < n` such that `3*p + 8` and `(p - 1)*n + 1` are both
prime.

For a prime `p` we have `p ≥ 2`, so the natural-number subtraction `p - 1` is the integer one.
-/

namespace OMA.S_oeis_a230243

theorem main : ∀ n : ℕ, 4 < n →
    ∃ p : ℕ, p < n ∧ p.Prime ∧ (3 * p + 8).Prime ∧ ((p - 1) * n + 1).Prime := by
  sorry

end OMA.S_oeis_a230243
