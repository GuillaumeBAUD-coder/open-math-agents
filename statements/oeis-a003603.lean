import Mathlib

/-!
# OEIS A003603: rows of the Wythoff array

Source: https://oeis.org/A003603
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` (A003603) is the row of the Wythoff array containing `n`, and A035612(n) is the column
containing `n` (rows and columns counted from `1`). Conjecture (OEIS entry):
`a(n) = |⌊n/φ⌋ - ⌊n (1/φ + 1/(-φ)^(A035612(n) + 1))⌋|`, where `φ = (1 + √5)/2`.

Conventions:
* The Wythoff array is `W(r, 1) = ⌊⌊rφ⌋φ⌋`, `W(r, 2) = ⌊⌊rφ⌋φ²⌋`,
  `W(r, c) = W(r, c-1) + W(r, c-2)` for `r ≥ 1`, `c ≥ 3`. Every positive integer occurs in it
  exactly once; row and column are taken as least indices, which is the same thing.
* `n ≥ 1` (offset `1`).
-/

namespace OMA.S_oeis_a003603

open Real

/-- The Wythoff array `W(r, c)` for `r, c ≥ 1` (values at index `0` are unused). -/
noncomputable def W (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => ⌊(⌊(r : ℝ) * goldenRatio⌋₊ : ℝ) * goldenRatio⌋₊
  | 2 => ⌊(⌊(r : ℝ) * goldenRatio⌋₊ : ℝ) * goldenRatio ^ 2⌋₊
  | c + 3 => W r (c + 2) + W r (c + 1)

/-- A003603: the row of the Wythoff array containing `n`. -/
noncomputable def row (n : ℕ) : ℕ :=
  sInf {r : ℕ | 1 ≤ r ∧ ∃ c, 1 ≤ c ∧ W r c = n}

/-- A035612: the column of the Wythoff array containing `n`. -/
noncomputable def col (n : ℕ) : ℕ :=
  sInf {c : ℕ | 1 ≤ c ∧ ∃ r, 1 ≤ r ∧ W r c = n}

/-- The conjectured closed form for A003603. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (row n : ℤ) = |⌊(n : ℝ) / goldenRatio⌋ -
      ⌊(n : ℝ) * (1 / goldenRatio + 1 / (-goldenRatio) ^ (col n + 1))⌋| := by
  sorry

end OMA.S_oeis_a003603
