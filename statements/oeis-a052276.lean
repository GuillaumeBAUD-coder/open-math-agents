import Mathlib

/-!
# OEIS A052276: Nonnegative numbers of the form n^3 ± 3

Source: https://oeis.org/A052276
Credit: @unserus

OEIS: "It is conjectured that A003325 and A052276 (the current sequence) have
infinitely many numbers in common, although only one example (128) is known."

A052276 lists the nonnegative `m` with `m = n^3 + 3` or `m = n^3 - 3` for some
`n ≥ 0`; the second form is written `m + 3 = n^3` to stay in `ℕ`.
A003325 lists the numbers `a^3 + b^3` with `a, b ≥ 1` (sums of two positive
cubes). The conjecture is that the intersection of the two sets is infinite.
(Example: `128 = 5^3 + 3 = 4^3 + 4^3`.)
-/

namespace OMA.S_oeis_a052276

/-- The terms of A052276: nonnegative numbers of the form `n^3 ± 3`. -/
def a052276Set : Set ℕ :=
  {m | ∃ n : ℕ, m = n ^ 3 + 3 ∨ m + 3 = n ^ 3}

/-- The terms of A003325: sums of two positive cubes. -/
def a003325Set : Set ℕ :=
  {m | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ m = a ^ 3 + b ^ 3}

/-- A003325 and A052276 have infinitely many terms in common. -/
theorem main : (a052276Set ∩ a003325Set).Infinite := by
  sorry

end OMA.S_oeis_a052276
