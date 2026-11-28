import Mathlib

/-!
# A331022: Numbers k such that the number of strict integer partitions of k is a power of 2.

Source: https://oeis.org/A331022
Credit: @keiichisince1986-bot

A331022 lists the numbers `k` such that the number of strict integer partitions of `k` (A000009)
is a power of `2`:
`0, 1, 2, 3, 4, 6, 9, 16, 20, 29, 34, 45`.
The entry states: Conjecture: This sequence is finite. (Next term `> 5·10^4` if it exists.)

Conventions:
- A strict integer partition of `k` is a partition of `k` into distinct parts. Mathlib's
  `Nat.Partition.distincts k` is the finset of partitions of `k` in which each part is used at
  most once, so its cardinality is A000009(k) (`= 1` for `k = 0`, matching the first term `0`).
- A power of `2` is `2 ^ j` for some `j : ℕ` (so `1 = 2^0` counts).
- The conjecture says that the set of such `k` is finite.
-/

namespace OMA.S_oeis_a331022

theorem main : {k : ℕ | ∃ j : ℕ, (Nat.Partition.distincts k).card = 2 ^ j}.Finite := by
  sorry

end OMA.S_oeis_a331022
