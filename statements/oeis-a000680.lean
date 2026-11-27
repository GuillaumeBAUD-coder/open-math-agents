import Mathlib

/-!
# A000680: a(n) = (2n)!/2^n

Source: https://oeis.org/A000680
Credit: @niclorusso

Conjecture (Werner Schulte, in the comments of A000680): For n > 0, (a(n) + 2^n) is a multiple of
(2n + 1) if and only if (2n + 1) is a prime number.

Conventions:
* a(n) = (2n)! / 2^n with offset 0. The division is exact (2^n divides (2n)!), so it is written
  with natural-number division.
-/

namespace OMA.S_oeis_a000680

/-- A000680: `a n = (2n)! / 2^n` (an exact division). -/
def a (n : ℕ) : ℕ := (2 * n).factorial / 2 ^ n

/-- Schulte's conjecture on A000680: for `n > 0`, `2n + 1` divides `a n + 2^n` if and only if
`2n + 1` is prime. -/
theorem main : ∀ n : ℕ, 0 < n → ((2 * n + 1 ∣ a n + 2 ^ n) ↔ (2 * n + 1).Prime) := by
  sorry

end OMA.S_oeis_a000680
