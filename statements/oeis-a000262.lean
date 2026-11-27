import Mathlib

/-!
# A000262: Number of sets of lists: number of partitions of {1,...,n} into any number of lists, where a list means an ordered subset.

Source: https://oeis.org/A000262
Credit: @darealpandaboi

Conjecture (stated as proved, see the Bala link on the OEIS page): for k = 2, 3, 4, ...,
the difference a(n+k) - a(n) is divisible by k.

Translation notes.
* The sequence is defined by the recurrence given on the OEIS page,
  a(n) = (2n-1) a(n-1) - (n-1)(n-2) a(n-2) with a(0) = a(1) = 1,
  which yields 1, 1, 3, 13, 73, 501, 4051, 37633, ... (the listed terms).
* Values are taken in ℤ so that the recurrence and the difference need no truncated subtraction.
* n ranges over all n >= 0, the offset of the sequence.
-/

namespace OMA.S_oeis_a000262

/-- A000262, by the recurrence a(n) = (2n-1) a(n-1) - (n-1)(n-2) a(n-2), a(0) = a(1) = 1. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => (2 * (n + 2 : ℤ) - 1) * a (n + 1) - ((n : ℤ) + 1) * n * a n

theorem main : ∀ k : ℕ, 2 ≤ k → ∀ n : ℕ, (k : ℤ) ∣ a (n + k) - a n := by
  sorry

end OMA.S_oeis_a000262
