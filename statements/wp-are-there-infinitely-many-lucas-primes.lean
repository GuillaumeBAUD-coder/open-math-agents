import Mathlib

/-!
# Are there infinitely many Lucas primes?

Source: https://en.wikipedia.org/wiki/Lucas_number#Lucas_primes
Credit: @cosmaticdev

Wikipedia (Lucas number): the Lucas numbers are `L 0 = 2`, `L 1 = 1`, and
`L n = L (n-1) + L (n-2)` for `n > 1`. A Lucas prime is a Lucas number that is prime
(first few: 2, 3, 7, 11, 29, 47, 199, 521, ...; OEIS A005479). It is an open question whether
there are infinitely many Lucas primes.

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_are_there_infinitely_many_lucas_primes

/-- The Lucas numbers `L n`: `L 0 = 2`, `L 1 = 1`, `L (n + 2) = L n + L (n + 1)`.
Source: https://en.wikipedia.org/wiki/Lucas_number (OEIS A000032). -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas n + lucas (n + 1)

/-- Are there infinitely many Lucas primes? I.e. the set of primes that are Lucas numbers
is infinite. -/
theorem main : Set.Infinite {p : ℕ | (∃ n : ℕ, lucas n = p) ∧ p.Prime} := by
  sorry

end OMA.S_wp_are_there_infinitely_many_lucas_primes
