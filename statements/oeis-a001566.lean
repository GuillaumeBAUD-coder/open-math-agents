import Mathlib

/-!
# A001566: a(0) = 3; thereafter, a(n) = a(n-1)^2 - 2.

Source: https://oeis.org/A001566
Credit: @rabdelaal

The Lucas–Lehmer-style sequence `a 0 = 3`, `a (n+1) = a n ^ 2 - 2` (OEIS A001566; the
reduced numerators of the convergents to `sqrt 5` by Newton's rule).

OEIS A001566 records the conjecture (Gerald McGarvey, 2004) that every term from `a 1`
on is congruent to `7` modulo `8`, i.e. of the form `8*a+7`.
-/

namespace OMA.S_oeis_a001566

/-- The OEIS A001566 entry: `a 0 = 3`, `a (n+1) = a n ^ 2 - 2`. -/
def a : ℕ → ℕ
  | 0 => 3
  | n + 1 => a n ^ 2 - 2

/-- The conjecture recorded in OEIS A001566 (McGarvey): every term `a n` with `n >= 1`
is of the form `8*a+7`. -/
theorem main : ∀ n ≥ 1, a n % 8 = 7 := by
  sorry

end OMA.S_oeis_a001566
