import Mathlib

/-!
# A069136: Numbers that are not the sum of 5 nonnegative cubes.

Source: https://oeis.org/A069136
Credit: @keiichisince1986-bot

A069136 lists the natural numbers that are not the sum of 5 nonnegative cubes:
`6, 7, 13, 14, 15, 20, 21, 22, 23, 34, 39, 41, 42, 46, 47, 48, 49, 50, 53, 58, 60, 61, 69, …`
The entry states: Sequence is conjectured to be finite.

Conventions:
- A sum of 5 nonnegative cubes is `x 0 ^ 3 + x 1 ^ 3 + x 2 ^ 3 + x 3 ^ 3 + x 4 ^ 3` for some
  `x : Fin 5 → ℕ`. Zero cubes are allowed, so this is the same as a sum of at most 5 positive
  cubes, and `0` is such a sum.
- The conjecture says that the set of natural numbers that are not such a sum is finite.
-/

namespace OMA.S_oeis_a069136

theorem main : {n : ℕ | ¬ ∃ x : Fin 5 → ℕ, n = ∑ i, x i ^ 3}.Finite := by
  sorry

end OMA.S_oeis_a069136
