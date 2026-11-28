import Mathlib

/-!
# A143836: T(r,c) = (prime(r+2) + prime(c+1))/2 (every integer >= 4 appears)

Source: https://oeis.org/A143836 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A143836 (offset 1): triangle read by rows: T(r,c) = (prime(r+2) + prime(c+1))/2, for
1 ≤ c ≤ r. Triangle begins
  4;
  5, 6;
  7, 8, 9;
  8, 9, 10, 12; ...

The entry records (Ya-Ping Lu, Mar 05 2023):

  Conjecture: Every integer >= 4 appears at least once in this sequence.

Reading of the source:
* `prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`.
* The triangle's entries are `T(r, c)` for `1 ≤ c ≤ r`. For such `c`, `prime(c+1)` and
  `prime(r+2)` are odd primes, so their sum is even and the halving is exact.
* "Every integer >= 4 appears": for every `m ≥ 4` there are `1 ≤ c ≤ r` with `T(r, c) = m`.
-/

namespace OMA.S_oeis_a143836

/-- `prime k`: the `k`-th prime, with `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- `T(r, c) = (prime(r+2) + prime(c+1)) / 2`. -/
noncomputable def T (r c : ℕ) : ℕ := (prime (r + 2) + prime (c + 1)) / 2

/-- Every integer `m ≥ 4` is an entry `T(r, c)` of the triangle (`1 ≤ c ≤ r`). -/
theorem main : ∀ m : ℕ, 4 ≤ m → ∃ r c : ℕ, 1 ≤ c ∧ c ≤ r ∧ T r c = m := by
  sorry

end OMA.S_oeis_a143836
