import Mathlib

/-!
# Are there infinitely many Lucas primes?

Source: https://en.wikipedia.org/wiki/Lucas_number#Lucas_primes
Credit: @mmiranda2

The Lucas numbers are defined by `L 0 = 2`, `L 1 = 1` and `L n = L (n - 1) + L (n - 2)` for
`n > 1`, giving `2, 1, 3, 4, 7, 11, 18, 29, 47, 76, ...` (OEIS A000032).
A *Lucas prime* is a Lucas number that is prime: `2, 3, 7, 11, 29, 47, 199, 521, 2207, ...`
(OEIS A005479). Note that `L 0 = 2` counts, as in the source's list.

It is an open question whether there are infinitely many Lucas primes. We state the
affirmative answer: the set of Lucas primes is infinite.
-/

namespace OMA.S_wp_are_there_infinitely_many_lucas_primes

/-- The Lucas numbers: `L 0 = 2`, `L 1 = 1`, `L (n + 2) = L (n + 1) + L n`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- A Lucas prime is a Lucas number that is prime. -/
def IsLucasPrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ n, lucas n = p

/-- There are infinitely many Lucas primes. -/
theorem main : {p : ℕ | IsLucasPrime p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_lucas_primes
