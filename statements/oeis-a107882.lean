import Mathlib

/-!
# Nested sums for OEIS A107882

Sources: https://oeis.org/A107882, https://oeis.org/A107880 and https://oeis.org/A107876.

This sequence is the column of index one in A107880, the square of A107876.
We use A107876's subpartition interpretation of the columns of its powers.
For column index c in the power p, the successive upper bounds start at p-1
and increase by c, c+1, and so on. Here the bounds begin 1, 2, 4, 7.
A subpartition is padded with zeros on the left. Its entries form a weakly
increasing list lying below these successive bounds. At index zero the list
is empty and the count is one.

Each nested-sum index runs from 1 to its upper bound inclusive. The initial
upper bound is 2, and after choosing i the next upper bound is i plus the
current increment. The increments start at 1 and then increase by one.
The proof checks the first six published terms.
-/

namespace OMA.S_oeis_a107882

def subparts : ℕ → ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _, _ => [[]]
  | remaining + 1, low, high, increment =>
    (List.range (high + 1 - low)).flatMap fun j =>
      (subparts remaining (low + j) (high + increment) (increment + 1)).map
        fun tail => (low + j) :: tail

def a (n : ℕ) : ℕ := (subparts n 0 1 1).length

def nested : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | remaining + 1, upper, increment =>
    ∑ j ∈ Finset.range upper, nested remaining (j + 1 + increment) (increment + 1)

theorem main : ∀ n : ℕ, a n = nested n 2 1 := by
  sorry

end OMA.S_oeis_a107882
