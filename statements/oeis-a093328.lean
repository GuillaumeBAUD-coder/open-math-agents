import Mathlib

/-!
# A093328: a(n) = 2*n^2 + 3

Source: https://oeis.org/A093328
Credit: @niclorusso

Conjecture (in the comments of A093328): no perfect powers.

Conventions:
* The sequence has offset 0: a(n) = 2n^2 + 3 for n >= 0.
* A perfect power is b ^ k with b > 1 and k > 1. (OEIS A001597 also lists 1, but every term is at
  least 3, so the conventions agree here.)
-/

namespace OMA.S_oeis_a093328

/-- `x` is a perfect power: `x = b ^ k` for some natural numbers `b > 1` and `k > 1`. -/
def IsPerfectPower (x : ℕ) : Prop :=
  ∃ b k : ℕ, 1 < b ∧ 1 < k ∧ b ^ k = x

/-- The conjecture on A093328: no term `2n^2 + 3` is a perfect power. -/
theorem main : ∀ n : ℕ, ¬ IsPerfectPower (2 * n ^ 2 + 3) := by
  sorry

end OMA.S_oeis_a093328
