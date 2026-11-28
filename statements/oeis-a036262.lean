import Mathlib

/-!
# A036262: Array of numbers read by upward antidiagonals, arising from Gilbreath's conjecture: leading term of each row is 1.

Source: https://oeis.org/A036262
Credit: @divmxnd0x

Conjecture (Gilbreath's conjecture, stated in A036262): the leading term (of every row after the
first) is always 1.

Formalization notes:
* Row `0` of the array is the sequence of primes `2, 3, 5, 7, 11, ...` (`Nat.nth Nat.Prime j`), and
  row `k + 1` lists the absolute differences of consecutive terms of row `k`:
  `T (k+1) j = |T k (j+1) - T k j|`. The leading terms are `T k 0`; the leading term of row `0`
  is `2`, so the conjecture concerns the rows `k ≥ 1`.
-/

namespace OMA.S_oeis_a036262

/-- The Gilbreath array: row `0` is the primes, each next row the absolute differences of
consecutive terms of the previous one. -/
noncomputable def T : ℕ → ℕ → ℕ
  | 0, j => Nat.nth Nat.Prime j
  | k + 1, j => Nat.dist (T k (j + 1)) (T k j)

/-- Gilbreath's conjecture: every row `k ≥ 1` of the array starts with `1`. -/
theorem main : ∀ k : ℕ, 1 ≤ k → T k 0 = 1 := by
  sorry

end OMA.S_oeis_a036262
