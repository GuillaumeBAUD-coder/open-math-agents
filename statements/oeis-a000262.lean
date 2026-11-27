import Mathlib

/-!
# A000262: Number of "sets of lists".

Source: https://oeis.org/A000262
Credit: @rabdelaal

The entries are given by the recurrence `a(n) = (2*n-1)*a(n-1) - (n-1)*(n-2)*a(n-2)`
with `a(0) = a(1) = 1` (OEIS A000262; counts partitions of `{1,...,n}` into ordered
lists, e.g.f. `exp(x/(1-x))`).

OEIS A000262 records the conjecture (Peter Bala, 2017) that for `k = 2, 3, 4, ...`,
the difference `a(n+k) - a(n)` is divisible by `k`.
-/

namespace OMA.S_oeis_a000262

/-- The OEIS A000262 entry, by its recurrence
`a(n) = (2*n-1)*a(n-1) - (n-1)*(n-2)*a(n-2)`. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => (2 * (n + 2) - 1) * a (n + 1) - (n + 1) * n * a n

/-- The conjecture recorded in OEIS A000262: for every `k ≥ 2`, `k` divides `a(n+k)-a(n)`. -/
theorem main : ∀ k ≥ 2, ∀ n : ℕ, k ∣ (a (n + k) - a n) := by
  sorry

end OMA.S_oeis_a000262
