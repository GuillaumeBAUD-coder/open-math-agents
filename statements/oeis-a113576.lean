import Mathlib

/-!
# A113576: least `(2n-1)`-digit palindromic prime congruent to `1` modulo `2n-1`.

Source: https://oeis.org/A113576
Credit: @cjchaffin

Conjecture (on the OEIS page): no term is zero, i.e. for every `n ≥ 1` such a prime exists.

Conventions: offset 1; a palindrome is a positive integer whose base-10 digits
(`Nat.digits 10`) equal their reverse; the digit length is exactly `2n-1`. The
congruence is `2n-1 ∣ p-1` (which holds automatically when `n=1`, matching `a(1)=2`).
The conjecture is formalized as existence, not the “least such prime” part of the name.
-/

namespace OMA.S_oeis_a113576

def IsOddPalindromicPrime (n p : ℕ) : Prop :=
  p.Prime ∧ (Nat.digits 10 p).length = 2 * n - 1 ∧
    (Nat.digits 10 p).reverse = Nat.digits 10 p ∧ 2 * n - 1 ∣ p - 1

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, IsOddPalindromicPrime n p := by
  sorry

end OMA.S_oeis_a113576
