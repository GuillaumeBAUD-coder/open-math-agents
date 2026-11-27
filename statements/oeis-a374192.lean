import Mathlib

/-!
# Reaching one of two cycles in the modified Collatz iteration (OEIS A374192)

Source: https://oeis.org/A374192, Gary Detlefs, June 30, 2024.
Credit: @MMexicann
-/

namespace OMA.S_oeis_a374192

def step (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else if n % 3 = 0 then 3 * n + 1 else n + 1

/-- The cycles are `1, 2` and `10, 5, 6, 3`. The source counts iterations up to the
first visit to either `1` or `10`, including a visit at time zero. -/
def ReachesCycle (n : ℕ) : Prop :=
  ∃ k : ℕ, (step^[k]) n = 1 ∨ (step^[k]) n = 10

theorem main : ∀ n : ℕ, 0 < n → ReachesCycle n := by
  sorry

end OMA.S_oeis_a374192
