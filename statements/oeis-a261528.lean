import Mathlib

/-!
# A261528: Least positive integer k such that both k and k*n belong to the set {m>0: prime(m)+2 is prime with prime(prime(m)+2) = prime(prime(m))+6}.

Source: https://oeis.org/A261528
Credit: @divmxnd0x

Let `S = {k > 0 : prime(k) + 2 is prime and prime(prime(k) + 2) = prime(prime(k)) + 6}`.

Conjecture (Zhi-Wei Sun, stated in A261528): Any positive rational number `r` can be written as
`m/n` with `m` and `n` in `S`. (This implies that there are infinitely many twin prime pairs
`{p, p + 2}` with `prime(p + 2) - prime(p) = 6`; the existence of `a(n)` is the case `r = n`.)

Formalization notes:
* `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`.
* With this definition the elements of `S` below 300 are 2, 3, 17, and `a(1) = 2`, matching the
  data of A261528.
-/

namespace OMA.S_oeis_a261528

/-- The `m`-th prime, `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ :=
  Nat.nth Nat.Prime (m - 1)

/-- The set `S` of A261528. -/
def S : Set ℕ :=
  {k | 0 < k ∧ (prime k + 2).Prime ∧ prime (prime k + 2) = prime (prime k) + 6}

/-- Sun's conjecture: every positive rational is `m/n` with `m, n ∈ S`. -/
theorem main : ∀ r : ℚ, 0 < r → ∃ m ∈ S, ∃ n ∈ S, r = (m : ℚ) / n := by
  sorry

end OMA.S_oeis_a261528
