import Mathlib

/-!
# A128440: rows 2n-1 and 2n of the array floor(k*phi^n) are disjoint

Source: https://oeis.org/A128440 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A128440 (offset 1): array T(n,k) = floor(k*r^n) where r = golden ratio = (1 + sqrt(5))/2, read by
descending antidiagonals. Rows 1 and 2 are the lower and upper Wythoff sequences (A000201,
A001950), which partition the positive integers. Corner:
  1  3  4  6  8 ...
  2  5  7 10 13 ...
  4  8 12 16 21 ...

The entry records (Clark Kimberling, Nov 11 2022):

  Conjecture: rows 2n-1 and 2n are disjoint for every positive integer n.

(A stronger conjecture of Nov 13 2022, about the relative order of the two rows, is not stated
here.)

Reading of the source:
* `T n k = ⌊k φ^n⌋` for `n, k ≥ 1`, with `φ = Real.goldenRatio`; rows are indexed by `n` and
  columns by `k`.
* "rows 2n-1 and 2n are disjoint": no value occurs in both, i.e. `T (2n-1) j ≠ T (2n) k` for all
  `j, k ≥ 1`, for every `n ≥ 1`. (For n = 1 this is the classical Beatty partition; for n ≥ 2,
  1/φ^(2n-1) + 1/φ^(2n) < 1, so the rows do not cover the integers and disjointness is the claim.)
-/

namespace OMA.S_oeis_a128440

/-- `T(n, k) = ⌊k φ^n⌋`. -/
noncomputable def T (n k : ℕ) : ℤ := ⌊(k : ℝ) * Real.goldenRatio ^ n⌋

/-- Kimberling's conjecture: rows `2n - 1` and `2n` have no common value. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ j k : ℕ, 1 ≤ j → 1 ≤ k → T (2 * n - 1) j ≠ T (2 * n) k := by
  sorry

end OMA.S_oeis_a128440
