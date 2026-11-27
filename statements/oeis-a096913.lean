import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.Group.Even

/-!
# Square terms of OEIS A096913

The sequence consists of numbers which become squares after adding their
largest decimal digit raised to their smallest decimal digit. The source
records an exhaustive computation by Maon Wenders in 2012.
Source: https://oeis.org/A096913 (OEIS Foundation, CC BY-SA 4.0).
Lean statement: @cjchaffin.
-/

namespace OMA.S_oeis_a096913

/-- Both digit extrema of zero are zero. Its offset is therefore zero to the zeroth power. -/
def digitPower (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).max?.getD 0) ^ ((Nat.digits 10 n).min?.getD 0)

theorem main : ∀ n : ℕ,
    (IsSquare n ∧ IsSquare (digitPower n + n)) ↔ n = 0 ∨ n = 3844 := by
  sorry

end OMA.S_oeis_a096913
