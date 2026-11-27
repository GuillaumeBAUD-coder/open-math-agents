import Mathlib

/-!
# A000041: a(n) is the number of partitions of n (the partition numbers).

Source: https://oeis.org/A000041
Credit: @darealpandaboi

Open conjectures on the OEIS page, stated together:
1. No a(n) has the form x^m with m > 1 and x > 1.
2. Each integer n > 2 different from 6 can be written as a sum of finitely many numbers of
   the form a(k) + 2 (k > 0) with no summand dividing another
   (Zhi-Wei Sun; verified for n <= 7140).

Translation notes.
* a(n) is the number of partitions of n, Fintype.card (Nat.Partition n); a(0) = 1.
* In part 2 no summand may divide another, so the summands are pairwise distinct
  (x divides x); they therefore form a finite set s, and the sum of s is n.
* The page also lists a conjecture of Gary W. Adamson (2013) on ordered compositions with
  signed pentagonal terms. It is marked there as true by the pentagonal number theorem
  (Joerg Arndt), so it is not included here.
* Checked by computer: part 1 holds for n <= 80 and part 2 holds for 2 < n <= 80, n /= 6
  (6 is the only exception in that range).
-/

namespace OMA.S_oeis_a000041

/-- A000041: the number of partitions of n. -/
def a (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

theorem main :
    (∀ n x m : ℕ, 1 < x → 1 < m → a n ≠ x ^ m) ∧
    (∀ n : ℕ, 2 < n → n ≠ 6 →
      ∃ s : Finset ℕ, (∀ t ∈ s, ∃ k : ℕ, 0 < k ∧ t = a k + 2) ∧
        (∀ t ∈ s, ∀ u ∈ s, t ≠ u → ¬ t ∣ u) ∧ ∑ t ∈ s, t = n) := by
  sorry

end OMA.S_oeis_a000041
