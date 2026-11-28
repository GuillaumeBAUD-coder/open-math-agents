import Mathlib

/-!
# A062854: First differences of A027424.

Source: https://oeis.org/A062854
Credit: @EmircanEsen

Conjecture (Thomas Ordowski, Jan 28 2017): a(n) > n/log(n) for n > 2.

Formalization notes:
* A027424(n) is the number of distinct products `i * j` with `1 ≤ i, j ≤ n` (the number of
  distinct entries of the `n × n` multiplication table); here `M n`, with `M 0 = 0`.
* A062854 (offset 1) is `a n = M n - M (n - 1)`: `a 1 = 1`, `a 4 = 9 - 6 = 3` (the OEIS
  example). `M` is monotone, so the natural subtraction is exact. These definitions reproduce
  the OEIS data.
* `log` is the natural logarithm. Checked numerically for `2 < n ≤ 3000`, where the ratio
  `a(n) / (n / log n)` stays above `1.039`.
-/

namespace OMA.S_oeis_a062854

/-- A027424: the number of distinct products `i * j` with `1 ≤ i, j ≤ n`. -/
def M (n : ℕ) : ℕ := ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).image fun p : ℕ × ℕ => p.1 * p.2).card

/-- A062854, offset 1: the first differences of A027424. -/
def a (n : ℕ) : ℕ := M n - M (n - 1)

/-- For every `n > 2`, `a n > n / log n`. -/
theorem main : ∀ n : ℕ, 2 < n → (n : ℝ) / Real.log n < a n := by
  sorry

end OMA.S_oeis_a062854
