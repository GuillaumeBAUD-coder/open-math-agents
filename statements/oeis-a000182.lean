import Mathlib

/-!
# A000182: Tangent (or "Zag") numbers: e.g.f. tan(x)

Source: https://oeis.org/A000182
Credit: @divmxnd0x

Conjecture 1 (Peter Bala, Dec 24 2021, stated in A000182): the sequence taken modulo any integer
`k` eventually becomes periodic with period dividing `phi(k)`.

Formalization notes:
* `a n` is the `n`-th tangent number (offset 1 as in the OEIS: `a 1, a 2, ... = 1, 2, 16, 272,
  7936, ...`, so that `tan x = ∑ a(n) x^(2n-1)/(2n-1)!`); `a 0 = 0` is a filler value that plays no
  role in the statement.
* The definition uses the recurrence `a(n) = ∑_{i=1}^{n-1} binomial(2n-2, 2i-1) a(i) a(n-i)` for
  `n ≥ 2`, `a(1) = 1` (formula in A000182; it is the coefficient form of `tan' = 1 + tan^2`).
* "Eventually periodic with period dividing `phi(k)`" is stated as: `phi(k)` is a period from
  some index on, i.e. there is `N` with `a(n + phi(k)) ≡ a(n) (mod k)` for all `n ≥ N` (a period
  divides `phi(k)` exactly when `phi(k)` is itself a period, the minimal eventual period dividing
  every eventual period). The conjecture is stated for every positive integer `k`.
-/

namespace OMA.S_oeis_a000182

/-- The tangent numbers: `a 1 = 1` and `a n = ∑_{i=1}^{n-1} binomial(2n-2, 2i-1) a(i) a(n-i)`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => ∑ j : Fin (n + 1),
      (2 * (n + 1)).choose (2 * j.val + 1) * a (j.val + 1) * a (n + 1 - j.val)
termination_by n => n
decreasing_by
  all_goals have := j.isLt
  all_goals omega

/-- Bala's conjecture 1: modulo every `k ≥ 1`, the tangent numbers are eventually periodic with
period dividing `phi(k)`. -/
theorem main : ∀ k : ℕ, 0 < k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    a (n + k.totient) ≡ a n [MOD k] := by
  sorry

end OMA.S_oeis_a000182
