import Mathlib

/-!
# OEIS A071685: non-palindromic n dividing or divided by their reversal

The sequence lists the non-palindromic natural numbers n, not divisible
by 10, such that either n divides its decimal digit-reversal R(n) or
R(n) divides n. The proven material (DemosMathNT, module A071685) shows
membership is equivalent to `R(n) = 4n`, `R(n) = 9n`, `n = 4 R(n)` or
`n = 9 R(n)`, the union of the four quotient families of the OEIS
comment.

The conjecture is the one stated by H. P. Dale on the OEIS page: every
term is congruent to 1, 12, 78 or 89 modulo 100. It has been verified
on the 26 terms of the DATA section only; the universal statement over
all terms is open. The spec encodes the sequence by a membership
predicate `isA071685` (there is no nth-term function), so the
quantification runs over all naturals satisfying the predicate.
Positional digits in Mathlib are little-endian, so `rev10` reverses
`Nat.digits 10 n` and trailing zeros of n drop out naturally.

Source: https://oeis.org/A071685
Conjecture: H. P. Dale.
-/

namespace OMA.S_oeis_a071685

/-- Decimal reversal of `n`: `ofDigits` of the reversed digit list.
    `rev10 0 = 0` and `rev10 (10 * k) = rev10 k`. -/
def rev10 (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- OEIS membership predicate: `n` is non-palindromic, `¬ 10 ∣ n`, and
    one of `n ∣ rev10 n`, `rev10 n ∣ n` holds. -/
def isA071685 (n : ℕ) : Prop :=
  ¬ List.Palindrome (Nat.digits 10 n) ∧ ¬ (10 ∣ n) ∧
    (n ∣ rev10 n ∨ rev10 n ∣ n)

instance decA071685 (n : ℕ) : Decidable (isA071685 n) :=
  inferInstanceAs (Decidable (¬ List.Palindrome (Nat.digits 10 n) ∧
    ¬ (10 ∣ n) ∧ (n ∣ rev10 n ∨ rev10 n ∣ n)))

theorem main : ∀ n : ℕ, isA071685 n →
    n % 100 = 1 ∨ n % 100 = 12 ∨ n % 100 = 78 ∨ n % 100 = 89 := by
  sorry

end OMA.S_oeis_a071685
