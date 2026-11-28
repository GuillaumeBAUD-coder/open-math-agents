import Mathlib

/-!
# A196935: number of 3-term APs of primes with middle term prime(n) and gap 6k.

Source: https://oeis.org/A196935
Credit: @cjchaffin

`a(n)` is the number of integers `k > 0` such that `prime(n) > 6k` and
`prime(n) - 6k`, `prime(n)`, `prime(n) + 6k` are all prime, where `prime(n)` is the
`n`-th prime (`prime(1) = 2`). Offset 5; e.g. `a(5) = 1` via `{5, 11, 17}`.

Conjecture (on the OEIS page): `a(n) > 0` for all `n ≥ 5`. Formalized as existence of
at least one such `k`, not the counting function itself.
-/

namespace OMA.S_oeis_a196935

/-- The `n`-th prime with `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

theorem main : ∀ n : ℕ, 5 ≤ n →
    ∃ k : ℕ, 0 < k ∧ 6 * k < prime n ∧
      (prime n - 6 * k).Prime ∧ (prime n + 6 * k).Prime := by
  sorry

end OMA.S_oeis_a196935
