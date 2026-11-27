import Mathlib

/-!
# A000009: Expansion of Product_{m >= 1} (1 + x^m); number of partitions of n into distinct parts; number of partitions of n into odd parts.

Source: https://oeis.org/A000009
Credit: @ZenimXD

The entry records two conjectures of Zhi-Wei Sun in its comments. `main` states both, as a
conjunction, in the order the source gives them.

Conjecture 1 (Zhi-Wei Sun, Apr 14 2023). Each positive integer n can be written as
a_1 + ... + a_k, where a_1, ..., a_k are strict partition numbers (i.e., terms of A000009) with no
one dividing another. Verified for n = 1..1350.

Conjecture 2 (Zhi-Wei Sun, May 20 2023). For each integer n > 7, a(n) divides none of p(n),
p(n) - 1 and p(n) + 1, where p(n) is the number of partitions of n (A000041). Verified for
n <= 10^5 (Sun) and n <= 2*10^6 (Vaclav Kotesovec, May 23 2023).

Reading of the source:
* `a n` is A000009(n), the number of partitions of n into distinct parts, with the entry's
  offset 0, so a(0) = 1. A strict partition number is any value `a m` with `m : ℕ`.
* The summands are indexed by `Fin k`, as a_1, ..., a_k in the source. No one dividing another
  is required for every pair of distinct positions i ≠ j. In particular no value can be used
  twice, and 1 can only appear when n = 1 (as the single summand).
* For conjecture 2, n ranges over the natural numbers n > 7 (the sequence is indexed by n ≥ 0),
  and divisibility is taken in ℤ so that p(n) - 1 is ordinary subtraction (p(n) ≥ 1 in any case).
-/

namespace OMA.S_oeis_a000009

/-- A000009(n): the number of partitions of `n` into distinct parts. -/
def a (n : ℕ) : ℕ := (Nat.Partition.distincts n).card

/-- A000041(n): the number of partitions of `n`. -/
def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

theorem main :
    -- Conjecture 1: every positive integer is a sum of strict partition numbers,
    -- no one of which divides another.
    (∀ n : ℕ, 0 < n →
      ∃ (k : ℕ) (b : Fin k → ℕ),
        (∀ i, ∃ m : ℕ, b i = a m) ∧
        (∀ i j, i ≠ j → ¬ b i ∣ b j) ∧
        ∑ i, b i = n) ∧
    -- Conjecture 2: for n > 7, a(n) divides none of p(n), p(n) - 1, p(n) + 1.
    (∀ n : ℕ, 7 < n →
      ¬ (a n : ℤ) ∣ (p n : ℤ) ∧ ¬ (a n : ℤ) ∣ (p n : ℤ) - 1 ∧ ¬ (a n : ℤ) ∣ (p n : ℤ) + 1) := by
  sorry

end OMA.S_oeis_a000009
