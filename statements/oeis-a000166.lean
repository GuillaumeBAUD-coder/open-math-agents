import Mathlib

/-!
# A000166: Subfactorial or rencontres numbers, or derangements: number of permutations of n elements with no fixed points.

Source: https://oeis.org/A000166
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a000166

/-- A000166: a(n) = number of permutations of n elements with no fixed points (subfactorial).
Mathlib's `numDerangements`. -/
abbrev a (n : ℕ) : ℕ := numDerangements n

/-- `m` is a perfect power: `m = b ^ k` with `k ≥ 2`. -/
def IsPerfectPower' (m : ℕ) : Prop := ∃ b k : ℕ, 2 ≤ k ∧ m = b ^ k

/-- Conjecture (Zhi-Wei Sun, Jan 2025): for n > 2, a(n) is a perfect power only for n = 4
(a(4) = 9 = 3^2). -/
theorem main : ∀ n : ℕ, 2 < n → (IsPerfectPower' (a n) ↔ n = 4) := by
  sorry

end OMA.S_oeis_a000166
