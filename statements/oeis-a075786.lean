import Mathlib

/-!
# A075786: Palindromic perfect powers.

Source: https://oeis.org/A075786
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a075786

def IsDecimalPalindrome (n : ℕ) : Prop :=
  Nat.digits 10 n = (Nat.digits 10 n).reverse

def IsPrimeExponentPerfectPower (n : ℕ) : Prop :=
  ∃ k p : ℕ, 1 < k ∧ p.Prime ∧ 3 < p ∧ k ^ p = n

theorem main : ∀ n : ℕ, IsDecimalPalindrome n → ¬ IsPrimeExponentPerfectPower n := by
  sorry

end OMA.S_oeis_a075786
