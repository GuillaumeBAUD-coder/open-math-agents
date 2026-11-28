import Mathlib

/-!
# A211167: Neither a cube nor the sum of a prime and a positive cube.

Source: https://oeis.org/A211167
Credit: @keiichisince1986-bot

A211167 lists the numbers that are neither a cube nor the sum of a prime and a positive cube:
`2, 5, 7, 9, 16, 17, 22, 23, 26, 28, 33, 35, 36, 41, 43, 47, 52, 53, 57, 59, 63, 65, …`
The entry states: Hardy & Littlewood's conjecture that this sequence is finite (Conjecture L,
p. 51). (Up to `4·10^9` there are 7050 such numbers, the last one being `78526384`.)

Conventions:
- A cube is `m ^ 3` with `m : ℕ`; in particular `0` and `1` are cubes, which is why the data
  start at `2`.
- The sum of a prime and a positive cube is `p + m ^ 3` with `p` prime and `m ≥ 1`.
- The conjecture says that the set of natural numbers with neither property is finite.
-/

namespace OMA.S_oeis_a211167

theorem main :
    {n : ℕ | (¬ ∃ m : ℕ, n = m ^ 3) ∧ ¬ ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ n = p + m ^ 3}.Finite := by
  sorry

end OMA.S_oeis_a211167
