import Mathlib

/-!
# A072933: Asymptotic density of exceptions to least k with floor((1+1/k)^m) = floor((1+1/m)^k)

Source: https://oeis.org/A072933
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Numbers m such that the least k such that floor((1+1/k)^m) = floor((1+1/m)^k) is not equal
to round(m*91/100).
Conjecture: lim_{n -> infinity} a(n)/n = 10.
-/

namespace OMA.S_oeis_a072933

open Filter Topology

/-- Least `k ≥ 1` such that `⌊(1 + 1/k)^m⌋ = ⌊(1 + 1/m)^k⌋`. -/
noncomputable def leastK (m : ℕ) : ℕ :=
  sInf { k : ℕ | 1 ≤ k ∧
    Nat.floor ((1 + (1 : ℚ) / (k : ℚ)) ^ m) = Nat.floor ((1 + (1 : ℚ) / (m : ℚ)) ^ k) }

/-- Predicate for membership in A072933. -/
def isTerm (m : ℕ) : Prop :=
  1 ≤ m ∧ (leastK m : ℤ) ≠ round ((m : ℝ) * 91 / 100)

/-- The `n`-th term of A072933 (0-indexed). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth isTerm n

theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) atTop (𝓝 10) := by
  sorry

end OMA.S_oeis_a072933
