import Mathlib

/-!
# OEIS A033485: `a(n) = a(n-1) + a(⌊n/2⌋)`, growth conjectures

Source: https://oeis.org/A033485
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(1) = 1`, `a(n) = a(n-1) + a(⌊n/2⌋)`. Conjectures (OEIS entry):
`lim_{n → ∞} (a(2n)/a(n)) · (log n)/n = c = 1.64…`, and `a(n)/A(n)` is bounded, where `A(n) = 1`
if `n` is a power of `2` and otherwise `A(n) = √n ∏_{k < log₂ n} (n/2^k) / log(n/2^k)`.

Conventions:
* Offset 1; `a 0 = 0` is a placeholder that the recurrence never reaches.
* `c = 1.64…` is read as `1.64 ≤ c < 1.65`. The product in `A(n)` runs over the integers
  `0 ≤ k < log₂ n`, i.e. `k ≤ ⌊log₂ n⌋` when `n` is not a power of `2`.
* 'Bounded' is over `n ≥ 1`.
-/

namespace OMA.S_oeis_a033485

open Classical

open Filter Topology

/-- The sequence. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => a (n + 1) + a ((n + 2) / 2)
decreasing_by all_goals omega

/-- The comparison function `A(n)`. -/
noncomputable def A (n : ℕ) : ℝ :=
  if ∃ j : ℕ, n = 2 ^ j then 1
  else Real.sqrt n * ∏ k ∈ Finset.range (Nat.log 2 n + 1),
    ((n : ℝ) / 2 ^ k) / Real.log ((n : ℝ) / 2 ^ k)

/-- Both growth conjectures. -/
theorem main :
    (∃ c : ℝ, 1.64 ≤ c ∧ c < 1.65 ∧
      Tendsto (fun n : ℕ => (a (2 * n) : ℝ) / a n * Real.log n / n) atTop (𝓝 c)) ∧
    (∃ B : ℝ, ∀ n : ℕ, 1 ≤ n → (a n : ℝ) / A n ≤ B) := by
  sorry

end OMA.S_oeis_a033485
