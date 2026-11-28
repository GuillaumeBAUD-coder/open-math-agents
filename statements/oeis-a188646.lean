import Mathlib

/-!
# A188646: Array of a(n)=a(n-1)*k-((k-1)/(k^n)) where a(0)=1 and k=(sqrt(x^2-1)+x)^2 for integers x>=1.

Source: https://oeis.org/A188646
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (by Charles L. Hohn, Apr 06 2011; square array with rows x = 1, 2, 3, ... and columns
n = 0, 1, 2, ..., e.g. row x = 2 is 1, 13, 181, 2521, 35113, ...) records in its COMMENTS section:

  Conjecture: Given function f(x, y)=(sqrt(x^2+y)+x)^2; constant k=f(x, y); and initial term
  a(0)=1; then for all integers x>=1 and y=[+-]1, k may be irrational, but sequence
  a(n)=a(n-1)*k-((k-1)/(k^n)) always produces integer sequences; y=-1 results shown here;
  y=1 results are A188647.

Conventions:
* `x` is a natural number with `1 ≤ x` and `y` is an integer with `y = 1` or `y = -1`.
* `k x y` is the real number `(sqrt(x^2 + y) + x)^2`, using `Real.sqrt`; since `x ≥ 1` and
  `y ≥ -1`, the radicand is nonnegative and `k x y > 0`.
* `a x y` is the real sequence with `a(0) = 1` and, for `n ≥ 1`,
  `a(n) = a(n-1) * k - (k - 1) / k^n`, exactly as in the entry (written with index `n + 1`).
* The conjecture says that every term is an integer: for all such `x`, `y` and every `n ≥ 0`,
  there is an integer `m` with `a(n) = m`. This covers both A188646 (`y = -1`) and A188647
  (`y = 1`), as the conjecture does.
-/

namespace OMA.S_oeis_a188646

/-- The constant `k = f(x, y) = (sqrt(x^2 + y) + x)^2` of the entry. -/
noncomputable def k (x : ℕ) (y : ℤ) : ℝ :=
  (Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ)) + (x : ℝ)) ^ 2

/-- The sequence `a(0) = 1`, `a(n) = a(n-1) * k - (k - 1) / k^n` for `n ≥ 1`. -/
noncomputable def a (x : ℕ) (y : ℤ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => a x y n * k x y - (k x y - 1) / k x y ^ (n + 1)

/-- The conjecture of A188646: for all integers `x ≥ 1` and `y = 1` or `y = -1`, every term
`a(n)` is an integer. -/
theorem main : ∀ x : ℕ, 1 ≤ x → ∀ y : ℤ, (y = 1 ∨ y = -1) →
    ∀ n : ℕ, ∃ m : ℤ, a x y n = (m : ℝ) := by
  sorry

end OMA.S_oeis_a188646
