import Mathlib

/-!
# Are there infinitely many palindromic primes to every base?

Source: https://en.wikipedia.org/wiki/Palindromic_prime
Credit: @Spenz90

A palindromic prime is a prime number whose representation in a given base
reads the same forwards and backwards; palindromicity depends on the base.
It is not known whether there are infinitely many palindromic primes in
base 10. The question stated here asks this for every base at once.
-/

namespace OMA.S_wp_are_there_infinitely_many_palindromic_primes_to_every_base

/-- A prime `p` is a palindromic prime in base `b` if the list of its
base-`b` digits is a palindrome. (`Nat.digits` lists digits from least to
most significant; a list is a palindrome if and only if its reverse is, so
this agrees with the written representation reading the same both ways.) -/
def IsPalindromicPrime (b p : ℕ) : Prop :=
  p.Prime ∧ List.Palindrome (Nat.digits b p)

/-- The open question: in every base `b ≥ 2`, are there infinitely many
palindromic primes? -/
theorem main : ∀ b : ℕ, 2 ≤ b → {p : ℕ | IsPalindromicPrime b p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_palindromic_primes_to_every_base
