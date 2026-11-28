import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.Palindrome
import Mathlib.Logic.Function.Iterate

/-!
# A006960: Reverse and Add! sequence starting with 196.

Source: https://oeis.org/A006960 (OEIS Foundation, CC BY-SA 4.0).
Credit: @xuan-CY

The conjecture in the entry's comments says that 196 is the smallest initial
term whose decimal reverse-and-add trajectory never reaches a palindrome.
The trajectory includes its starting term at index zero, as in the OEIS entry.
-/

namespace OMA.S_oeis_a006960

/-- Add a nonnegative integer to the integer obtained by reversing its decimal
digits. Mathlib's digits and ofDigits both use little-endian order; reversing
the digit list between them implements decimal reversal. Leading zeros in the
reversed representation are discarded when the list is read as an integer. -/
def reverseAndAdd (n : ℕ) : ℕ :=
  n + Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- The reverse-and-add trajectory with arbitrary starting value, indexed from
zero. In particular, trajectory 196 is OEIS A006960. -/
def trajectory (start steps : ℕ) : ℕ :=
  reverseAndAdd^[steps] start

/-- The 196 conjecture, including the asserted minimality of the starting value.
All starting values are natural numbers. Mathlib represents zero by the empty
digit list, which is palindromic, so zero already reaches a palindrome at step
zero, consistently with the ordinary decimal representation of zero. -/
theorem main :
    (∀ steps : ℕ, ¬ (Nat.digits 10 (trajectory 196 steps)).Palindrome) ∧
      ∀ start : ℕ, start < 196 →
        ∃ steps : ℕ, (Nat.digits 10 (trajectory start steps)).Palindrome := by
  sorry

end OMA.S_oeis_a006960

