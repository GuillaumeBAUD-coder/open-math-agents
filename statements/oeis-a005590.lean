import Mathlib

/-!
# A005590: a(0) = 0, a(1) = 1, a(2n) = a(n), a(2n+1) = a(n+1) - a(n).

Source: https://oeis.org/A005590
Credit: @divmxnd0x

Conjecture (Ralf Stephan, May 02 2003, stated in A005590): `a(3n) = 0` iff `n` is in A003714.

Formalization notes:
* A003714 (the fibbinary numbers) are the numbers whose binary representation contains no two
  adjacent 1's, i.e. `n &&& (n >>> 1) = 0`.
* The conjecture is stated for all `n ≥ 0` (offset 0 of both sequences; `a 0 = 0` and `0` is a
  fibbinary number).
-/

namespace OMA.S_oeis_a005590

/-- A005590: `a 0 = 0`, `a 1 = 1`, `a (2n) = a n`, `a (2n+1) = a (n+1) - a n`. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if h : (n + 2) % 2 = 0 then a ((n + 2) / 2) else a ((n + 2) / 2 + 1) - a ((n + 2) / 2)
decreasing_by all_goals omega

/-- `n` is a fibbinary number (A003714): no two adjacent 1's in binary. -/
def IsFibbinary (n : ℕ) : Prop := n &&& (n >>> 1) = 0

/-- Stephan's conjecture: `a(3n) = 0` iff `n` is fibbinary. -/
theorem main : ∀ n : ℕ, a (3 * n) = 0 ↔ IsFibbinary n := by
  sorry

end OMA.S_oeis_a005590
