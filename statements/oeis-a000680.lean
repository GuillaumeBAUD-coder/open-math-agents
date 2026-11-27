import Mathlib

/-!
# A000680: a(n) = (2n)!/2^n.

Source: https://oeis.org/A000680
Credit: @rabdelaal

OEIS A000680 records the conjecture that for `n > 0`, `a(n) + 2^n` is a multiple of `2n + 1`
if and only if `2n + 1` is prime, where `a(n) = (2n)!/2^n`.
-/

namespace OMA.S_oeis_a000680

/-- The OEIS A000680 sequence: `a(n) = (2n)! / 2^n`. -/
def a (n : ℕ) : ℕ :=
  Nat.factorial (2 * n) / 2 ^ n

/-- For `n > 0`, `a(n) + 2^n` is a multiple of `2n + 1` iff `2n + 1` is prime
(conjecture recorded in OEIS A000680). -/
theorem main : ∀ n > 0, (2 * n + 1 ∣ a n + 2 ^ n) ↔ Nat.Prime (2 * n + 1) := by
  sorry

end OMA.S_oeis_a000680
