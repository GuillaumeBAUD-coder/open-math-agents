import Mathlib

/-!
# A002457: a(n) = (2n+1)!/n!^2.

Source: https://oeis.org/A002457
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a002457

/-- A002457: a(n) = (2n+1)! / (n!)^2 (the division is exact). -/
def a (n : ℕ) : ℕ := (2 * n + 1).factorial / (n.factorial) ^ 2

/-- Conjecture (Joseph M. Shunia, Sep 2025): for n > 0,
a(n) = floor(sqrt((16^n + 1)^(2n+1))) mod 16^n. `Nat.sqrt` is the integer (floor) square root. -/
theorem main : ∀ n : ℕ, 0 < n → a n = Nat.sqrt ((16 ^ n + 1) ^ (2 * n + 1)) % 16 ^ n := by
  sorry

end OMA.S_oeis_a002457
