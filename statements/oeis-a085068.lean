import Mathlib

/-!
A085068: Number of steps >= 1 for iteration of map x -> (4/3)*ceiling(x) to reach an integer when started at n, or -1 if no such integer is reached.

Source: https://oeis.org/A085068
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

It is conjectured that an integer is always reached.
-/

namespace OMA.S_oeis_a085068

def step (x : ℚ) : ℚ := (4 / 3 : ℚ) * (⌈x⌉ : ℚ)

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ ∃ m : ℤ, (step^[k]) (n : ℚ) = (m : ℚ) := by
  sorry

end OMA.S_oeis_a085068
