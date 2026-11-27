import Mathlib

/-!
# A214498: Smallest k>=0 such that (3^n+k)*2^n-1 and (3^n+k)*2^n+1 are a twin prime pair.

Source: https://oeis.org/A214498
Credit: @sntntHb

Conjecture (stated on the OEIS page): there is always one such `k` for each `n > 0`, i.e. for every
positive integer `n` there is `k ≥ 0` such that `(3^n + k) * 2^n - 1` and `(3^n + k) * 2^n + 1` are
both prime.

Existence of some such `k` is equivalent to existence of the smallest one. For `n > 0` the number
`(3^n + k) * 2^n` is at least `6`, so the natural-number subtraction is the integer one.
-/

namespace OMA.S_oeis_a214498

theorem main : ∀ n : ℕ, 0 < n →
    ∃ k : ℕ, ((3 ^ n + k) * 2 ^ n - 1).Prime ∧ ((3 ^ n + k) * 2 ^ n + 1).Prime := by
  sorry

end OMA.S_oeis_a214498
