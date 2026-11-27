import Mathlib

/-!
# A002627: a(n) = n*a(n-1) + 1, a(0) = 0.

Source: https://oeis.org/A002627
Credit: @rabdelaal

OEIS A002627 records the conjecture (R. J. Mathar, 2014) that the sequence satisfies
the linear recurrence `a(n) + (n-1)*a(n-2) = (n+1)*a(n-1)` for `n >= 2`, i.e.
`a(n) + (-n-1)*a(n-1) + (n-1)*a(n-2) = 0`.
-/

namespace OMA.S_oeis_a002627

/-- The OEIS A002627 entry: `a 0 = 0`, `a (n+1) = (n+1) * a n + 1`. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) * a n + 1

/-- The conjecture recorded in OEIS A002627 (Mathar): for `n >= 2`,
`a(n) + (n-1)*a(n-2) = (n+1)*a(n-1)`. -/
theorem main : ∀ n ≥ 2, a n + (n - 1) * a (n - 2) = (n + 1) * a (n - 1) := by
  sorry

end OMA.S_oeis_a002627
