import Mathlib

/-!
# A261339: Least positive integer k such that both k and k*n belong to the set {m>0: m+1, m^2+1 and m^2+prime(m)^2 are all prime}.

Source: https://oeis.org/A261339
Credit: @divmxnd0x

Let `S = {m > 0 : m + 1, m^2 + 1 and m^2 + prime(m)^2 are all prime}`.

Conjecture (Zhi-Wei Sun, stated in A261339): `a(n)` exists for any `n > 0`. In general, any positive
rational number `r` can be written as `m/n` with `m` and `n` in `S`. (The existence of `a(n)` is the
case `r = n`.)

Formalization notes:
* `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`.
* With this definition the least `k` with `k, k n ∈ S` is 1, 1, 2, 1 for `n = 1, 2, 5, 10`, matching
  the data of A261339.
-/

namespace OMA.S_oeis_a261339

/-- The set `S` of A261339. -/
def S : Set ℕ :=
  {m | 0 < m ∧ (m + 1).Prime ∧ (m ^ 2 + 1).Prime ∧ (m ^ 2 + Nat.nth Nat.Prime (m - 1) ^ 2).Prime}

/-- Sun's conjecture: every positive rational is `m/n` with `m, n ∈ S`. -/
theorem main : ∀ r : ℚ, 0 < r → ∃ m ∈ S, ∃ n ∈ S, r = (m : ℚ) / n := by
  sorry

end OMA.S_oeis_a261339
