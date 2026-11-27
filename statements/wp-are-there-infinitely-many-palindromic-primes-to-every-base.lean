import Mathlib

/-!
# Are there infinitely many palindromic primes to every base?

Source: https://en.wikipedia.org/wiki/palindromic_prime
Credit: @cosmaticdev

The source (Wikipedia, Palindromic prime) states that it is not known whether there are
infinitely many palindromic primes in base 10. The problem as titled asks this for every
base: for each base `b >= 2`, are there infinitely many primes whose base-`b` expansion
reads the same forwards and backwards?

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_are_there_infinitely_many_palindromic_primes_to_every_base

/-- A prime `p` is a base-`b` palindromic prime if its base-`b` digits (`Nat.digits b p`,
most significant digit first, no leading zeros) read the same forwards and backwards.
Source: https://en.wikipedia.org/wiki/palindromic_prime -/
def IsBasePalindromicPrime (b p : ℕ) : Prop :=
  p.Prime ∧ (Nat.digits b p).Palindrome

/-- Are there infinitely many palindromic primes to every base? I.e. for every base
`b >= 2`, the set of primes `p` whose base-`b` expansion is a palindrome is infinite. -/
theorem main : ∀ b : ℕ, 2 ≤ b → Set.Infinite {p : ℕ | IsBasePalindromicPrime b p} := by
  sorry

end OMA.S_wp_are_there_infinitely_many_palindromic_primes_to_every_base
