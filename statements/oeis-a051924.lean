import Mathlib

/-!
# A051924: a(n) = binomial(2n,n) - binomial(2n-2,n-1)

Source: https://oeis.org/A051924
Credit: @niclorusso

Conjecture (Gary Detlefs, in the comments of A051924): a(n) mod n^2 = n+2 iff n is an odd prime.

Conventions:
* The sequence has offset 1: a(n) = binomial(2n, n) - binomial(2n-2, n-1) for n >= 1. Since
  binomial(2n-2, n-1) <= binomial(2n, n), the subtraction in the natural numbers is exact.
* "a(n) mod n^2" is the least nonnegative residue, `a n % n ^ 2`.
-/

namespace OMA.S_oeis_a051924

/-- A051924: `a n = binomial(2n, n) - binomial(2n-2, n-1)` (for `n >= 1`). -/
def a (n : ℕ) : ℕ := (2 * n).choose n - (2 * n - 2).choose (n - 1)

/-- Detlefs' conjecture on A051924: for `n >= 1`, `a(n) mod n^2 = n + 2` if and only if `n` is an
odd prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n % n ^ 2 = n + 2 ↔ (n.Prime ∧ Odd n)) := by
  sorry

end OMA.S_oeis_a051924
