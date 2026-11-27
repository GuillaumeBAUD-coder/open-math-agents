import Mathlib.Data.Int.Basic

/-!
# A relation between the convergents to the square root of five

Creighton Dement recorded this identity in OEIS A001076 on November 28, 2004.
Both entries start at index zero. Their common recurrence comes from the
repeating partial quotient four, with the initial values used in the two entries.

https://oeis.org/A001076 and https://oeis.org/A001077
Credit: @ZedingZhang
-/

namespace OMA.S_oeis_a001076

def convergentSequence (first second : ℤ) : ℕ → ℤ
  | 0 => first
  | 1 => second
  | n + 2 => 4 * convergentSequence first second (n + 1) + convergentSequence first second n

/-- OEIS A001076, including its initial denominator zero. -/
abbrev denominator : ℕ → ℤ := convergentSequence 0 1

/-- OEIS A001077, including its initial numerator one. -/
abbrev numerator : ℕ → ℤ := convergentSequence 1 2

theorem main : ∀ n : ℕ,
    2 * denominator (n + 1) = denominator (n + 2) - numerator (n + 1) := by
  sorry

end OMA.S_oeis_a001076
