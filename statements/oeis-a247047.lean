import Mathlib

/-!
# A247047: k^2, k^3, k^4 with exactly 2, 3, 4 distinct digits (only 6, 8, 15)

Source: https://oeis.org/A247047 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A247047 (offset 1): numbers k such that k^2 contains exactly 2 distinct digits and k^3 contains
exactly 3 distinct digits; data 5, 6, 8, 9, 15, 30, 173, 300, 3000, ...

The entry records:

  The numbers k such that k^2 contains 2 distinct digits, k^3 contains 3 distinct digits, and
  k^4 contains 4 distinct digits are conjectured to only be 6, 8, and 15. (Intersection of
  A016069, A155146, and A155150.)

Reading of the source:
* Digits are base-10 digits (`Nat.digits 10`), and "contains exactly d distinct digits" means the
  set of digits of the number has `d` elements.
* `k` ranges over the positive integers.
* "are conjectured to only be 6, 8, and 15": the set of such `k` is exactly `{6, 8, 15}`.
-/

namespace OMA.S_oeis_a247047

/-- The number of distinct base-10 digits of `x`. -/
def distinctDigits (x : ℕ) : ℕ := (Nat.digits 10 x).toFinset.card

/-- The only positive `k` with `k^2`, `k^3`, `k^4` having exactly 2, 3, 4 distinct digits are
6, 8 and 15. -/
theorem main :
    {k : ℕ | 0 < k ∧ distinctDigits (k ^ 2) = 2 ∧ distinctDigits (k ^ 3) = 3 ∧
      distinctDigits (k ^ 4) = 4} = {6, 8, 15} := by
  sorry

end OMA.S_oeis_a247047
