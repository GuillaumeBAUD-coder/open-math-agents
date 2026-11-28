import Mathlib

/-!
# A006450: Prime-indexed primes: primes with prime subscripts.

Source: https://oeis.org/A006450
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A006450): the sequence `a(n)^(1/n)` (`n = 1, 2, 3, ...`) is
strictly decreasing. (An analog of the Firoozbakht conjecture on primes.)

Formalization notes:
* `prime k` is the `k`-th prime with `prime 1 = 2` (`Nat.nth Nat.Prime (k - 1)`), and
  `a n = prime (prime n)` with offset 1: `a 1, a 2, ... = 3, 5, 11, 17, 31, ...`.
* `a(n)^(1/n)` is the real `n`-th root; strictly decreasing means `a(n+1)^(1/(n+1)) < a(n)^(1/n)`
  for every `n ≥ 1`.
-/

namespace OMA.S_oeis_a006450

/-- The `k`-th prime, `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- A006450(n): the prime whose index is the `n`-th prime. -/
noncomputable def a (n : ℕ) : ℕ := prime (prime n)

/-- Sun's conjecture: `a(n)^(1/n)` is strictly decreasing for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a (n + 1) : ℝ) ^ (1 / ((n : ℝ) + 1)) < (a n : ℝ) ^ (1 / (n : ℝ)) := by
  sorry

end OMA.S_oeis_a006450
