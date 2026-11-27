import Mathlib

/-!
# A000166: Subfactorial or rencontres numbers, or derangements.

Source: https://oeis.org/A000166
Credit: @rabdelaal

OEIS A000166 records the conjecture that `a(n)` with `n > 2` is a perfect power only for
`n = 4`, where `a(4) = 3 ^ 2` (verified up to `n = 1000`). Here `a(n)` is the number of
derangements of an `n`-element set, `numDerangements n` in Mathlib, and "perfect power"
is read as `a(n) = a ^ b` with `a > 1` and `b > 1`.
-/

namespace OMA.S_oeis_a000166

/-- `n` is a perfect power when `n = a ^ b` with `a > 1` and `b > 1`. -/
def IsPerfectPowerNat (n : ℕ) : Prop :=
  ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ n = a ^ b

/-- A derangement count `numDerangements n` with `n > 2` is a perfect power only for
`n = 4` (conjecture recorded in OEIS A000166; the value there is `numDerangements 4 = 9 =
3 ^ 2`). -/
theorem main : ∀ n > 2, IsPerfectPowerNat (numDerangements n) → n = 4 := by
  sorry

end OMA.S_oeis_a000166
