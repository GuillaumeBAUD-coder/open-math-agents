import Mathlib

/-!
# A002063: a(n) = 9*4^n.

Source: https://oeis.org/A002063
Credit: @bnb9001

The OEIS entry says that the terms 9 * 4^n are squares that can be written as a sum of exactly
two distinct powers of two (for instance 9 * 4^4 = 2304 = 2^11 + 2^8), and conjectures that they
are the only squares with this property (Andres Cicuttin; tested on squares up to (10^7)^2).

We state the full characterization the entry asserts: a natural number is a square that is a sum
of two distinct powers of two if and only if it is of the form 9 * 4^n. The direction
`Set.range ⊆ ...` is the stated fact; the direction `... ⊆ Set.range` is the conjecture.
Distinct powers are encoded as `2 ^ i + 2 ^ j` with `i < j` (exponents are natural numbers, so
the powers of two are 1, 2, 4, ...).
-/

namespace OMA.S_oeis_a002063

/-- The squares that are a sum of exactly two distinct powers of two are exactly the numbers
`9 * 4 ^ n`. -/
theorem main :
    {m : ℕ | IsSquare m ∧ ∃ i j : ℕ, i < j ∧ m = 2 ^ i + 2 ^ j} =
      Set.range (fun n : ℕ => 9 * 4 ^ n) := by
  sorry

end OMA.S_oeis_a002063
