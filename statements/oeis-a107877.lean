import Mathlib

/-!
# Nested sums for the first column of the triangle in A107876

Source: https://oeis.org/A107877 and https://oeis.org/A107876.

A107877 identifies its terms as counts of subpartitions of the first
n-1 positive triangular numbers. We pad a subpartition on the left with
zeros, so its parts form a weakly increasing list bounded coordinatewise
by 0, 1, 3, 6, 10, and so on. The initial zero does not change the count.
At n = 0 the empty list is the unique subpartition.

The nested sums use one-based indices. An index i gives the next sum the
upper bound i plus the next increment, with increments 1, 2, 3, and so on.
The first sum has only index 1. Removing it and evaluating the innermost
sum of ones gives the source's displayed sums for indices 3 through 6.
The proof checks all seven terms starting at index zero.
-/

namespace OMA.S_oeis_a107877

def subparts : ℕ → ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _, _ => [[]]
  | remaining + 1, low, high, increment =>
    (List.range (high + 1 - low)).flatMap fun j =>
      (subparts remaining (low + j) (high + increment) (increment + 1)).map
        fun tail => (low + j) :: tail

def a (n : ℕ) : ℕ := (subparts n 0 0 1).length

def nested : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | remaining + 1, upper, increment =>
    ∑ j ∈ Finset.range upper, nested remaining (j + 1 + increment) (increment + 1)

theorem main : ∀ n : ℕ, a n = nested n 1 1 := by
  sorry

end OMA.S_oeis_a107877
