import Mathlib

/-!
# A103673: If in binary representation n! contains 5! then 1 else 0.

Source: https://oeis.org/A103673
Credit: @EmircanEsen

Conjecture (Charles R Greathouse IV, Apr 07 2013): a(n) = 1 for n > 65.

Formalization notes:
* "Contains" means the binary string of `5! = 120`, namely `1111000`, occurs as a contiguous
  block of the binary string of `n!`.
* `Nat.digits 2` lists binary digits least significant first. Reversing both lists preserves
  being a contiguous block, so the containment is `List.IsInfix` of the two digit lists.
* These definitions reproduce the OEIS data (`a 5 = 1`, `a 10 = 1`, `a 12 = 1`, …). The last
  `n ≤ 65` with `a n = 0` is `n = 65`, and there is none for `65 < n < 3000`.
-/

namespace OMA.S_oeis_a103673

/-- A103673: `1` if the binary digits of `5!` occur as a block of those of `n!`, else `0`. -/
def a (n : ℕ) : ℕ :=
  if (Nat.digits 2 (Nat.factorial 5)).IsInfix (Nat.digits 2 n.factorial) then 1 else 0

/-- For every `n > 65`, `a n = 1`. -/
theorem main : ∀ n : ℕ, 65 < n → a n = 1 := by
  sorry

end OMA.S_oeis_a103673
