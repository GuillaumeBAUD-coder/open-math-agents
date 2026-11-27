import Mathlib

/-!
# A001652: a(n) = 6*a(n-1) - a(n-2) + 2 with a(0) = 0, a(1) = 3.

Source: https://oeis.org/A001652

Conjecture (Vaclav Kotesovec, Jun 02 2015): for `n > 1`, `a(n)` is the index of the first
occurrence of `n` in the sequence A123737.

A123737 (offset 1) is the sequence of partial sums of `(-1)^floor(k*sqrt(2))`:
`b(m) = Sum_{k=1..m} (-1)^floor(k*sqrt(2))`, which begins `-1, 0, 1, 0, -1, 0, -1, -2, …`.
A001652 begins `0, 3, 20, 119, 696, 4059, …`; for example the value `2` first appears in A123737
at index `20 = a(2)`.

Encoding:
- `a` is computed in `ℕ`. The sequence is nondecreasing (`a(n+2) ≥ 5 * a(n+1) + 2`), so
  `6 * a (n + 1) ≥ a n` and the natural-number subtraction never truncates.
- `b m` is the partial sum over `k = 1, …, m`, so it is indexed exactly as A123737 (offset 1);
  `floor(k*sqrt(2))` is `⌊(k : ℝ) * √2⌋₊`, as `k * √2 ≥ 0`.
- The index of the first occurrence of `n` is the least index `m ≥ 1` of the sequence
  (A123737 starts at index 1) with `b m = n`; `IsLeast` also asserts that `n` occurs.
-/

namespace OMA.S_oeis_a001652

/-- OEIS A001652: `0, 3, 20, 119, 696, …` -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | n + 2 => 6 * a (n + 1) - a n + 2

/-- OEIS A123737 (offset 1): the partial sums of `(-1)^floor(k * sqrt 2)` for `k = 1, …, m`. -/
noncomputable def b (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 m, (-1 : ℤ) ^ ⌊(k : ℝ) * Real.sqrt 2⌋₊

/-- Kotesovec's conjecture: for `n > 1`, `a(n)` is the first index at which A123737 equals `n`. -/
theorem main : ∀ n : ℕ, 1 < n → IsLeast {m : ℕ | 1 ≤ m ∧ b m = n} (a n) := by
  sorry

end OMA.S_oeis_a001652
