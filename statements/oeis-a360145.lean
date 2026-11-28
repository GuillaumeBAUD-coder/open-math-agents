import Mathlib

/-!
# A360145: Middle column of a reverse pyramid

Source: https://oeis.org/A360145
Pyramid definition: https://oeis.org/A359087
Related sequence: https://oeis.org/A132894
This is Bernard Schott's conjecture for the entire middle column. The apex special
case is Theorem 53 of Sela Fried, https://arxiv.org/abs/2607.24832.

The reverse pyramid of order `n` begins with the row
`1, 2, …, n-1, n, n-1, …, 2, 1` and replaces each interior position by
the sum of its three neighbors including itself. The top row is counted as row one.

A132894 counts horizontal steps across all length-`m` walks with height increments
`-1, 0, 1` that start at zero and never go below zero. We count walks and their
horizontal steps by partitioning them according to their first step.
-/

namespace OMA.S_oeis_a360145

/-- Entry at displacement `i` after `m` sweeps of the order-`n` pyramid.
The intended row has `i.natAbs + m < n`, so extending the base by zeros
outside its support does not affect its entries. -/
def row (n : ℕ) : ℕ → ℤ → ℕ
  | 0, i => n - i.natAbs
  | m + 1, i => row n m (i - 1) + row n m i + row n m (i + 1)

/-- Entry in row `k` of the middle column of the order-`n` reverse pyramid. -/
def T (n k : ℕ) : ℕ := row n (k - 1) 0

/-- Number of length-`m` walks starting at height `h` and staying nonnegative. -/
def walks : ℕ → ℕ → ℕ
  | 0, _ => 1
  | m + 1, 0 => walks m 0 + walks m 1
  | m + 1, h + 1 => walks m h + walks m (h + 1) + walks m (h + 2)

/-- Total number of horizontal steps over the same family of walks. The horizontal
first step contributes one for each walk in its tail class. -/
def horizontal : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, 0 => horizontal m 0 + horizontal m 1 + walks m 0
  | m + 1, h + 1 => horizontal m h + horizontal m (h + 1) +
      horizontal m (h + 2) + walks m (h + 1)

/-- A132894. -/
def b (m : ℕ) : ℕ := horizontal m 0

/-- Schott's conjectured formula for the entire middle column. -/
theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n → T n k = 3 ^ (k - 1) * n - 2 * b (k - 1) := by
  sorry

end OMA.S_oeis_a360145
