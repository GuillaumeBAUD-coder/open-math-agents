import Mathlib

/-!
# A261281: Least positive integer k with prime(k)^2-2 and prime(prime(k))^2-2 both prime such that prime(k*n)^2-2 and prime(prime(k*n))^2-2 are all prime.

Source: https://oeis.org/A261281
Credit: @divmxnd0x

Let `S = {k > 0 : prime(k)^2 - 2 and prime(prime(k))^2 - 2 are both prime}`.

Conjecture (Zhi-Wei Sun, stated in A261281): `a(n)` exists for any `n > 0`. In general, any positive
rational number `r` can be written as `m/n` with `m` and `n` in `S`. (The existence of `a(n)` is the
case `r = n`.)

Formalization notes:
* `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`; since
  `prime(m)^2 ≥ 4`, `prime(m) ^ 2 - 2` in `ℕ` is the integer `prime(m)^2 - 2`.
* With this definition the least `k` with `k, k n ∈ S` is 1, 1, 34, 2 for `n = 1, 2, 5, 7`,
  matching the data of A261281.
-/

namespace OMA.S_oeis_a261281

/-- The `m`-th prime, `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ :=
  Nat.nth Nat.Prime (m - 1)

/-- The set `S` of A261281. -/
def S : Set ℕ :=
  {k | 0 < k ∧ (prime k ^ 2 - 2).Prime ∧ (prime (prime k) ^ 2 - 2).Prime}

/-- Sun's conjecture: every positive rational is `m/n` with `m, n ∈ S`. -/
theorem main : ∀ r : ℚ, 0 < r → ∃ m ∈ S, ∃ n ∈ S, r = (m : ℚ) / n := by
  sorry

end OMA.S_oeis_a261281
