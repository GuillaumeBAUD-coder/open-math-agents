import Mathlib

/-!
# A000166: Subfactorial or rencontres numbers, or derangements

Source: https://oeis.org/A000166
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, Jan 09 2025, in the comments of A000166): a(n) with n > 2 is a perfect
power only for n = 4, with a(4) = 3^2. This has been verified for n <= 1000.

Conventions:
* a(n) is Mathlib's `numDerangements n`, the number of permutations of n elements with no fixed
  points, with the OEIS offset 0: a(0) = 1, a(1) = 0, a(2) = 1, a(3) = 2, a(4) = 9.
* A perfect power is m ^ k with m > 1 and k > 1. (OEIS A001597 also lists 1 as a perfect power,
  but a(n) >= 2 for every n > 2, so the two conventions agree on the range of the conjecture.)
* "is a perfect power only for n = 4, with a(4) = 3^2" is stated as an equivalence: for n > 2,
  a(n) is a perfect power if and only if n = 4.
-/

namespace OMA.S_oeis_a000166

/-- `n` is a perfect power: `n = m ^ k` for some natural numbers `m > 1` and `k > 1`. -/
def IsPerfectPower (n : ℕ) : Prop :=
  ∃ m k : ℕ, 1 < m ∧ 1 < k ∧ m ^ k = n

/-- Sun's conjecture on A000166: for `n > 2`, the number of derangements of `n` elements is a
perfect power if and only if `n = 4` (where it equals `3 ^ 2`). -/
theorem main : ∀ n : ℕ, 2 < n → (IsPerfectPower (numDerangements n) ↔ n = 4) := by
  sorry

end OMA.S_oeis_a000166
