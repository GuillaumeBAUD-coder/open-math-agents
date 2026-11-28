import Mathlib

/-!
# A379907: Triangle read by rows: T(n, k) = Sum_{i=0..n-k} (-1)^(n - k - i) * binomial(n - k, i) * binomial(k + 2*i, i) * (k + 1) / (k + 1 + i)

Source: https://oeis.org/A379907
Credit: @xor2k

The title is cut off in our copy of the data after `(k + 1) / (k + 1 + `; it was completed to
`(k + 1) / (k + 1 + i)`, the natural completion (the ballot numbers
binomial(k + 2*i, i) * (k + 1) / (k + 1 + i)).

Conjecture in the formula section of A379907 (the second of the two conjectures of the entry):
  T(n, k) = T(n, k-1) + T(n-1, k-1) - T(n-1, k-2) - T(n-2, k-2) for 2 <= k <= n.
Only this conjecture is formalized. The first conjecture of the entry, a general statement about
products of Riordan arrays, is not part of this statement.

Conventions:
* Offset 0: rows n = 0, 1, 2, ... and columns 0 <= k <= n.
* `T n k` is defined in ℚ exactly by the formula of the title, the division being done in ℚ
  (each summand is in fact an integer, see below). The sum runs over i = 0, ..., n - k.
* The recurrence is stated for all 2 <= k <= n. All entries that occur, T(n, k), T(n, k-1),
  T(n-1, k-1), T(n-1, k-2), T(n-2, k-2), have their column index within 0, ..., row index, so
  no extension of the formula outside the triangle is used (the natural subtraction `n - k` of
  the definition is exact on all of them).

Numerical check: a Python copy of the definition (exact rationals) gives integer summands and the
rows 1; 0, 1; 1, 1, 1; 1, 2, 2, 1; 3, 4, 4, 3, 1; 6, 9, 9, 7, 4, 1; 15, 21, 21, 17, 11, 5, 1;
36, 51, 51, 42, 29, 16, 6, 1 (the OEIS DATA field is not available offline for comparison;
column 0 is 1, 0, 1, 1, 3, 6, 15, 36, the Riordan numbers), and confirms the recurrence for
2 <= k <= n < 30.
-/

namespace OMA.S_oeis_a379907

/-- A379907 (offset 0): the triangle entry T(n, k), by the formula of the title, in ℚ. -/
def T (n k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n - k + 1),
    (-1 : ℚ) ^ (n - k - i) * (Nat.choose (n - k) i : ℚ) * (Nat.choose (k + 2 * i) i : ℚ)
      * ((k : ℚ) + 1) / ((k : ℚ) + 1 + (i : ℚ))

/-- The conjectured recurrence: T(n, k) = T(n, k-1) + T(n-1, k-1) - T(n-1, k-2) - T(n-2, k-2)
for 2 <= k <= n. -/
theorem main : ∀ n k : ℕ, 2 ≤ k → k ≤ n →
    T n k = T n (k - 1) + T (n - 1) (k - 1) - T (n - 1) (k - 2) - T (n - 2) (k - 2) := by
  sorry

end OMA.S_oeis_a379907
