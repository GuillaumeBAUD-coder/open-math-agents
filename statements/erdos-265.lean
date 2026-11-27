import Mathlib

/-!
# Erdős Problem 265

Source: https://www.erdosproblems.com/265
Credit: @shc261392

The source: let `1 ≤ a₁ < a₂ < ⋯` be an increasing sequence of integers. How fast can `aₙ → ∞`
grow if `∑ 1/aₙ` and `∑ 1/(aₙ - 1)` are both rational?

The source records that Kovač and Tao [KoTa24] almost completely solved this, showing that such a
sequence can grow doubly exponentially (`aₙ ^ (1/βⁿ) → ∞` for some `β > 1`), that a folklore
result rules out `lim aₙ ^ (1/2ⁿ) = ∞`, and that it remains open whether one can achieve
`limsup aₙ ^ (1/2ⁿ) > 1`. This file states that remaining open question, in its affirmative form:
a proof of `main` answers it yes, a proof of `¬ main` answers it no.

Reading used here:
* The sequence is `a : ℕ → ℕ`, strictly increasing, with `2 ≤ a 0`, so that every `1/(aₙ - 1)` is
  defined (the source's `1 ≤ a₁` with `a₁ = 1` would make `1/(a₁ - 1)` undefined).
* "`∑ 1/aₙ` is rational" means the series converges and its sum is a rational number; the same
  for `∑ 1/(aₙ - 1)`.
* `limsup aₙ ^ (1/2ⁿ) > 1` is written without `limsup` (which is a junk value in `ℝ` for an
  unbounded sequence) as: there is `c > 1` with `c < aₙ ^ (1/2ⁿ)` for infinitely many `n`.
* The indexing starts at `0`; shifting the index by one changes `1/2ⁿ` into `1/2ⁿ⁺¹`, which does
  not change whether such a `c > 1` exists.
-/

namespace OMA.S_erdos_265

open Filter

theorem main :
    ∃ a : ℕ → ℕ, StrictMono a ∧ 2 ≤ a 0 ∧
      Summable (fun n => 1 / (a n : ℝ)) ∧ (∃ q : ℚ, ∑' n, 1 / (a n : ℝ) = q) ∧
      Summable (fun n => 1 / ((a n : ℝ) - 1)) ∧ (∃ q : ℚ, ∑' n, 1 / ((a n : ℝ) - 1) = q) ∧
      ∃ c : ℝ, 1 < c ∧ ∃ᶠ n in atTop, c < (a n : ℝ) ^ ((1 : ℝ) / 2 ^ n) := by
  sorry

end OMA.S_erdos_265
