import Mathlib

/-!
# A002104: Logarithmic numbers.

Source: https://oeis.org/A002104
Credit: @rabdelaal

The entries satisfy `a(0) = 0, a(1) = 1` and the recurrence (Forberg)
`a(n) = n*a(n-1) - (n-1)*a(n-2) + 1` (OEIS A002104; e.g.f. `-log(1-x)*exp(x)`).

OEIS A002104 records the conjecture (R. J. Mathar, 2012) that the sequence satisfies
the linear recurrence `a(n) - (n+1)*a(n-1) + 2*(n-1)*a(n-2) - (n-2)*a(n-3) = 0` for
`n >= 3`.
-/

namespace OMA.S_oeis_a002104

/-- The OEIS A002104 entry: `a 0 = 0`, `a 1 = 1`,
`a (n+2) = (n+2) * a (n+1) - (n+1) * a n + 1`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (n + 2) * a (n + 1) - (n + 1) * a n + 1

/-- The conjecture recorded in OEIS A002104 (Mathar): for `n >= 3`,
`a(n) = (n+1)*a(n-1) - 2*(n-1)*a(n-2) + (n-2)*a(n-3)`. -/
theorem main : ∀ n ≥ 3,
    a n = (n + 1) * a (n - 1) - 2 * (n - 1) * a (n - 2) + (n - 2) * a (n - 3) := by
  sorry

end OMA.S_oeis_a002104
