import Mathlib.Data.Nat.Basic

/-!
# Binary replacement lengths in A289077

Source: https://oeis.org/A289077
Credit: @blakestone-x

Each pass reads the old word from left to right, consuming nonoverlapping matches.
The reference follows the OEIS table, generating function and program. They give a(7)=74, a(8)=114 and a(9)=176, and start the recurrence at n=10. Applying it at n=7 as printed would give 75. The proof checks this discrepancy separately.
-/

namespace OMA.S_oeis_a289077

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 11
  | 4 => 18
  | 5 => 30
  | 6 => 47
  | 7 => 74
  | 8 => 114
  | 9 => 176
  | n+10 => 2 * reference (n+9) + reference (n+8) - 4 * reference (n+7) + 2 * reference (n+6) + reference (n+5) - 2 * reference (n+4) + reference (n+3)

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false, false, true, false] ++ rewrite w
  | false :: true :: w => [false, true, true] ++ rewrite w
  | true :: false :: w => [true, false, false] ++ rewrite w
  | true :: true :: w => true :: rewrite (true :: w)

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a289077
