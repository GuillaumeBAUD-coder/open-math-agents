import Mathlib

/-!
# A165742: gaps between consecutive numbers 2^i * 7^j tend to infinity

Source: https://oeis.org/A165742 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A165742 (offset 1): first differences of A003591, the numbers of the form 2^i*7^j with
i, j >= 0 (1, 2, 4, 7, 8, 14, 16, 28, ...); data 1, 2, 3, 1, 6, 2, 12, 4, 17, 7, 8, 34, ...
(the 5th number of the form 2^i*7^j is 8 and the 6th is 14, so a(5) = 6).

The entry records (Charles R Greathouse IV, Jun 28 2011):

  Conjecturally, the limit infimum is infinite.

Reading of the source:
* `b n` (for `n ≥ 1`) is the `n`-th number of the form 2^i 7^j (`i, j ≥ 0`) in increasing order:
  `Nat.nth` (which counts from 0) at `n - 1`. There are infinitely many such numbers.
* `a n = b (n+1) - b n`; the sequence is increasing, so the difference is exact.
* "the limit infimum is infinite" for a sequence of naturals is the same as `a(n) → ∞`.
-/

namespace OMA.S_oeis_a165742

open Filter

/-- `x` is of the form `2^i * 7^j` with `i, j ≥ 0`. -/
def IsForm (x : ℕ) : Prop := ∃ i j : ℕ, x = 2 ^ i * 7 ^ j

/-- A003591(n): the `n`-th number of the form `2^i * 7^j` (`n ≥ 1`). -/
noncomputable def b (n : ℕ) : ℕ := Nat.nth IsForm (n - 1)

/-- A165742(n) = A003591(n+1) - A003591(n). -/
noncomputable def a (n : ℕ) : ℕ := b (n + 1) - b n

/-- The gaps tend to infinity (their limit inferior is infinite). -/
theorem main : Tendsto a atTop atTop := by
  sorry

end OMA.S_oeis_a165742
