import Mathlib

/-!
# A088113: a(n) = digit reversal of (11^n) divided by 11.

Source: https://oeis.org/A088113
Credit: @darealpandaboi

Conjecture: there are finitely many palindromic terms.

Translation notes.
* The digit reversal of m is the number whose decimal digits are those of m in reverse order;
  11^n never ends in 0, so no digit is lost. The reversal of 11^n is divisible by 11 (checked for
  n < 3000), and a(n) is the quotient, n >= 1 (offset 1). This reproduces the listed data
  1, 11, 121, 1331, 13651, 150161, ... (checked by computer).
* A term is palindromic when its decimal digit list equals its reverse. The statement says the set
  of palindromic values a(n), n >= 1, is finite. Among n < 4000 only n = 1, 2, 3, 4 give one.
* The question How many are palindromes and the divisibility observation are not conjectures.
-/

namespace OMA.S_oeis_a088113

/-- The decimal digit reversal of m. -/
def rev (m : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 m).reverse

/-- a(n) = rev(11^n) / 11. -/
def a (n : ℕ) : ℕ := rev (11 ^ n) / 11

theorem main :
    {m : ℕ | ∃ n : ℕ, 0 < n ∧ m = a n ∧ (Nat.digits 10 m).reverse = Nat.digits 10 m}.Finite := by
  sorry

end OMA.S_oeis_a088113
