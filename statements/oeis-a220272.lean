import Mathlib

/-!
# A220272: Number of ways to write n=x^2+y (x>0, y>0) with 2*x*y-1 prime.

Source: https://oeis.org/A220272
Credit: @keiichisince1986-bot

A220272 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n)>0 for all n>2.

Conventions:
- `a(n) > 0` means that there is at least one such representation: positive integers `x, y`
  with `n = x^2 + y` and `2xy - 1` prime (here `2xy ≥ 2`, so `2xy - 1` is not truncated).
-/

namespace OMA.S_oeis_a220272

theorem main :
    ∀ n : ℕ, 2 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x ^ 2 + y ∧ (2 * x * y - 1).Prime := by
  sorry

end OMA.S_oeis_a220272
