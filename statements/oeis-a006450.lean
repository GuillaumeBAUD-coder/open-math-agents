import Mathlib

/-!
# A006450: Prime-indexed primes: primes with prime subscripts.

Source: https://oeis.org/A006450
Credit: @MartinFoxy

The entry carries the comment (Zhi-Wei Sun, Aug 17 2015): I conjecture that the sequence
`a(n)^(1/n)` (n = 1,2,3,...) is strictly decreasing. This is an analog of the Firoozbakht
conjecture on primes.

Formalization notes:
* The sequence has offset 1 and `a(n) = prime(prime(n))`, where `prime(k)` is the `k`-th prime
  with `prime(1) = 2` (data from n = 1: 3, 5, 11, 17, 31, 41, 59, ...).
* Mathlib's `Nat.nth Nat.Prime` counts from 0, so `prime(k) = Nat.nth Nat.Prime (k - 1)` for
  `k ≥ 1`.
* Strictly decreasing over n = 1,2,3,... is stated as: for all `1 ≤ m < n`, the `n`-th root of
  `a(n)` is less than the `m`-th root of `a(m)`. The roots are real powers `x ^ (1 / n)`.
-/

namespace OMA.S_oeis_a006450

/-- The `k`-th prime for `k ≥ 1`, with `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- A006450 (offset 1): `a(n) = prime(prime(n))`. -/
noncomputable def a (n : ℕ) : ℕ := prime (prime n)

/-- Zhi-Wei Sun's conjecture: the sequence `a(n)^(1/n)`, `n = 1, 2, 3, ...`, is strictly
decreasing. -/
theorem main : ∀ m n : ℕ, 1 ≤ m → m < n →
    (a n : ℝ) ^ ((1 : ℝ) / (n : ℝ)) < (a m : ℝ) ^ ((1 : ℝ) / (m : ℝ)) := by
  sorry

end OMA.S_oeis_a006450
