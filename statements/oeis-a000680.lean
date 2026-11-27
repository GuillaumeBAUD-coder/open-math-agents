import Mathlib

/-!
# A000680: a(n) = (2n)!/2^n.

Source: https://oeis.org/A000680
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a000680

/-- A000680: a(n) = (2n)! / 2^n (the division is exact). -/
def a (n : ℕ) : ℕ := (2 * n).factorial / 2 ^ n

/-- Conjecture (Werner Schulte, Oct 2025): for n > 0, a(n) + 2^n is a multiple of 2n+1
if and only if 2n+1 is prime. -/
theorem main : ∀ n : ℕ, 0 < n → ((2 * n + 1 ∣ a n + 2 ^ n) ↔ Nat.Prime (2 * n + 1)) := by
  sorry

end OMA.S_oeis_a000680
