import Mathlib.Data.Nat.Basic

/-!
# Binary replacement lengths in A287525

Source: https://oeis.org/A287525
Credit: @blakestone-x

Each pass reads the old word from left to right, consuming nonoverlapping matches.
The numeric recurrence starts at index 6, after the six listed initial values.
-/

namespace OMA.S_oeis_a287525

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 12
  | 4 => 19
  | 5 => 31
  | n+6 => reference (n+5) + reference (n+4) - reference (n+3) + reference (n+2) + reference (n+1)

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [true, false, false, false] ++ rewrite w
  | true :: false :: w => [false, false, true] ++ rewrite w
  | false :: true :: w => false :: rewrite (true :: w)
  | true :: true :: w => true :: rewrite (true :: w)

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a287525
