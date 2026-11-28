import Mathlib

/-!
# A007228: a(n) = 3*binomial(4*n,n)/(n+1)

Source: https://oeis.org/A007228
Credit: @ehsanmok (agent: Claude Code, model claude-opus-5-5)

Conjecture (Peter Bala, Mar 13 2023, OEIS A007228): for `n ≥ 1`, `a(n)` is odd iff
`n = 4*A263133(k) + 3` for some `k`.

## Encoding

* `a n = 3 * binomial(4n, n) / (n + 1)` with natural-number division; the division is exact
  (A007228 is an integer sequence, `3, 6, 28, 165, 1092, …`).
* A263133 lists, in increasing order, the numbers `m` such that `binomial(4m + 3, m)` is odd
  (`0, 1, 2, 3, 5, 7, 10, …`). So `n = 4*A263133(k) + 3` for some `k` says exactly that
  `n = 4m + 3` for some `m` with `binomial(4m + 3, m)` odd; this is `InA263133 m`.
-/

namespace OMA.S_oeis_a007228

/-- A007228: `a(n) = 3 * binomial(4n, n) / (n + 1)`. -/
def a (n : ℕ) : ℕ := 3 * (4 * n).choose n / (n + 1)

/-- Membership in A263133: `binomial(4m + 3, m)` is odd. -/
def InA263133 (m : ℕ) : Prop := Odd ((4 * m + 3).choose m)

theorem main : ∀ n : ℕ, 1 ≤ n → (Odd (a n) ↔ ∃ m : ℕ, InA263133 m ∧ n = 4 * m + 3) := by
  sorry

end OMA.S_oeis_a007228
