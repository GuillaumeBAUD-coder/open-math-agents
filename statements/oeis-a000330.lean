import Mathlib

/-!
# OEIS A000330: square pyramidal numbers

Conjecture (Altug Alkan) stated in the comments of https://oeis.org/A000330 :
every integer can be represented as a sum of three generalized square pyramidal numbers,
where generalized means that negative indices are included.

Only this conjecture is stated here. The same comment mentions a related pentagonal case
(A336205) and a stronger version for generalized r-gonal pyramidal numbers for all r ≥ 3;
those are separate statements and are not formalized in this file.

The square pyramidal numbers are `0^2 + 1^2 + ... + k^2 = k (k + 1) (2 k + 1) / 6`.
Their generalization to all integers `k` uses the same polynomial, so for example
index `-1` gives `0`, index `-2` gives `-1` and index `-3` gives `-5`.

*References:*
- [A000330](https://oeis.org/A000330)
- [A336205](https://oeis.org/A336205) (the related pentagonal case, not stated here)
-/

namespace OMA.S_oeis_a000330

/-- The generalized square pyramidal number with index `k : ℤ`, namely `k (k + 1) (2 k + 1) / 6`.
The product `k (k + 1) (2 k + 1)` is always divisible by `6`, so the division is exact. -/
def genSqPyramidal (k : ℤ) : ℤ := k * (k + 1) * (2 * k + 1) / 6

/-- Conjecture (OEIS A000330): every integer is the sum of three generalized square pyramidal
numbers. -/
theorem main : ∀ n : ℤ, ∃ a b c : ℤ,
    n = genSqPyramidal a + genSqPyramidal b + genSqPyramidal c := by
  sorry

end OMA.S_oeis_a000330
