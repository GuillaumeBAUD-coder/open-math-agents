import Mathlib

/-!
# A008839: powers of 5 with no zero digit (5^58 is the last one)

Source: https://oeis.org/A008839 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A008839: numbers k such that the decimal expansion of 5^k contains no zeros; data
0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 17, 18, 30, 33, 58.

The entry records (N. J. A. Sloane, Feb 10 2023, corrected by Patrick De Geest, Jun 09 2024):

  Here is 5^58, conjecturally the largest power of 5 that does not contain a 0:
  34694469519536141888238489627838134765625.

Reading of the source:
* The decimal expansion of `x` is `Nat.digits 10 x`; it "contains a 0" when 0 is one of its
  digits (leading zeros are not digits, and 5^k > 0).
* "5^58 is the largest power of 5 that does not contain a 0": for every exponent `k > 58`, the
  decimal expansion of 5^k contains the digit 0. (That 5^58 itself has no 0 is a finite check
  shown in the entry; it is not part of the conjecture.)
-/

namespace OMA.S_oeis_a008839

/-- Every power 5^k with k > 58 has a 0 among its decimal digits. -/
theorem main : ∀ k : ℕ, 58 < k → 0 ∈ Nat.digits 10 (5 ^ k) := by
  sorry

end OMA.S_oeis_a008839
