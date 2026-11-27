import Mathlib

/-!
# A098608: a(n) = 100^n

Source: https://oeis.org/A098608
Credit: @niclorusso

Conjecture (in the comments of A098608): a(n) are the only positive squares (in base 10) with
digits in {0,1}.

Conventions:
* The sequence has offset 0: a(n) = 100^n for n >= 0, so its terms are 1, 100, 10000, ...
* "digits in {0,1}": every decimal digit of m (`Nat.digits 10 m`) is 0 or 1.
* "the only" is stated as a set equality: the positive squares whose decimal digits are all 0 or 1
  are exactly the numbers 100^n (each 100^n = (10^n)^2 is one).
-/

namespace OMA.S_oeis_a098608

/-- The conjecture on A098608: the positive squares with all decimal digits in `{0, 1}` are
exactly the powers of 100. -/
theorem main :
    {m : ℕ | 0 < m ∧ IsSquare m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1} =
      Set.range (fun n : ℕ => 100 ^ n) := by
  sorry

end OMA.S_oeis_a098608
