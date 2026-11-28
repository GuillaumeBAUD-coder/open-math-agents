import Mathlib

/-!
# A000926: Euler's "numerus idoneus" (or "numeri idonei", or idoneal, or suitable, or convenient numbers).

Source: https://oeis.org/A000926
Credit: @divmxnd0x

Conjecture (stated in A000926): the list of 65 idoneal numbers given there is complete.
(Chowla showed that the list is finite and Weinberger that there are at most two further terms.)

Formalization notes:
* Idoneal numbers are characterized here by the classical criterion (Euler; see the comments and
  references of A000926): a positive integer `n` is idoneal if and only if it cannot be written as
  `a b + b c + c a` with integers `0 < a < b < c`. With this definition the idoneal numbers up to
  `20000` are exactly the 65 terms of A000926.
* The conjecture says that the set of idoneal numbers is exactly the 65 listed terms.
-/

namespace OMA.S_oeis_a000926

/-- `n` is idoneal: `n > 0` and `n ≠ a b + b c + c a` for all `0 < a < b < c`. -/
def IsIdoneal (n : ℕ) : Prop :=
  0 < n ∧ ¬ ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ n = a * b + b * c + c * a

/-- The 65 known idoneal numbers. -/
def knownIdoneal : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 18, 21, 22, 24, 25, 28, 30, 33, 37, 40, 42, 45,
    48, 57, 58, 60, 70, 72, 78, 85, 88, 93, 102, 105, 112, 120, 130, 133, 165, 168, 177, 190, 210,
    232, 240, 253, 273, 280, 312, 330, 345, 357, 385, 408, 462, 520, 760, 840, 1320, 1365, 1848}

/-- The list of idoneal numbers in A000926 is complete. -/
theorem main : {n : ℕ | IsIdoneal n} = ↑knownIdoneal := by
  sorry

end OMA.S_oeis_a000926
