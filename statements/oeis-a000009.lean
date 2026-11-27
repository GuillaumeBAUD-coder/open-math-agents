import Mathlib

/-!
# A000009: number of partitions of `n` into distinct parts

Source: https://oeis.org/A000009
Credit: @STRML

The sequence `a(n)` (A000009) counts the partitions of `n` into distinct positive parts; by
Euler's theorem it also counts the partitions of `n` into odd parts. The two conjectures stated
below are Zhi-Wei Sun's (May 2023), quoted from the OEIS entry. `p(n)` is the partition number
A000041, the number of partitions of `n`.

This file only states the conjectures: the body of `main` stays `sorry`.
-/

open scoped BigOperators

namespace OMA.S_oeis_a000009

/-- `p(n)`: the number of partitions of `n` (A000041). -/
noncomputable def partitionNumber (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- `a(n)`: the number of partitions of `n` into distinct parts (A000009). -/
noncomputable def distinctPartitionNumber (n : ℕ) : ℕ := (Nat.Partition.distincts n).card

/--
Zhi-Wei Sun's two conjectures on A000009, as stated on the OEIS page.

1. Every positive integer `n` can be written as `a₁ + ... + aₖ` where the `aᵢ` are terms of
   A000009 and no one divides another.
2. For every integer `n > 7`, `a(n)` divides none of `p(n)`, `p(n) - 1`, `p(n) + 1`.

For `n > 7` we have `p(n) ≥ 5`, so the natural-number subtraction `p(n) - 1` is the ordinary
integer difference.
-/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ k : ℕ, ∃ a : Fin k → ℕ,
      (∀ i : Fin k, ∃ m : ℕ, a i = distinctPartitionNumber m) ∧
      (∀ i j : Fin k, i ≠ j → ¬ a i ∣ a j) ∧
      (∑ i : Fin k, a i) = n) ∧
    (∀ n : ℕ, 7 < n →
      ¬ (distinctPartitionNumber n ∣ partitionNumber n) ∧
      ¬ (distinctPartitionNumber n ∣ partitionNumber n - 1) ∧
      ¬ (distinctPartitionNumber n ∣ partitionNumber n + 1)) := by
  sorry

end OMA.S_oeis_a000009
