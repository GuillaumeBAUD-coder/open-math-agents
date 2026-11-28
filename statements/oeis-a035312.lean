import Mathlib

/-!
# OEIS A035312: Zorach additive triangle

Source: https://oeis.org/A035312

Each number is the sum of its west and northwest neighbours; the number in column 1 is the
least positive integer such that the row has no repeats with the numbers already in the table.
Conjecture: the triangle (read by rows) is a permutation of the positive integers.

Conventions.
- Rows `n ≥ 0` have entries `T n k`, `0 ≤ k ≤ n`. Given the earlier rows and a first entry `x`,
  row `n` is `r 0 = x`, `r (k+1) = r k + T (n-1) k`.
- `x` is admissible if `x ≥ 1` and no entry of the resulting row already occurs in rows `< n`
  (entries within a row are strictly increasing, so they never repeat each other). The first
  entry is the least admissible `x`. This determines `T` uniquely (`T 0 0 = 1`, row 1 is `2, 3`,
  row 2 is `4, 6, 9`, …), so we quantify over all `T` with these properties.
- Since all entries are distinct by construction, the conjecture is that every positive integer
  occurs.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a035312

/-- Row `n` built from first entry `x` and the previous row of `T`. -/
def rowFrom (T : ℕ → ℕ → ℕ) (n x : ℕ) : ℕ → ℕ
  | 0 => x
  | (k + 1) => rowFrom T n x k + T (n - 1) k

/-- `x` is an admissible first entry for row `n`. -/
def Admissible (T : ℕ → ℕ → ℕ) (n x : ℕ) : Prop :=
  1 ≤ x ∧ ∀ k ≤ n, ∀ i < n, ∀ j ≤ i, rowFrom T n x k ≠ T i j

/-- `T` is the Zorach additive triangle. -/
def IsZorach (T : ℕ → ℕ → ℕ) : Prop :=
  ∀ n : ℕ, Admissible T n (T n 0) ∧ (∀ x < T n 0, ¬ Admissible T n x) ∧
    ∀ k ≤ n, T n k = rowFrom T n (T n 0) k

theorem main :
    ∀ T : ℕ → ℕ → ℕ, IsZorach T → ∀ m : ℕ, 1 ≤ m → ∃ n k : ℕ, k ≤ n ∧ T n k = m := by
  sorry

end OMA.S_oeis_a035312
