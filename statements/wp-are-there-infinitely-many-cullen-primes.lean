import Mathlib

/-!
# Are there infinitely many Cullen primes?

Source: https://en.wikipedia.org/wiki/Cullen_number
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: the Cullen numbers are `C n = n * 2 ^ n + 1` for `n ≥ 1`; a Cullen prime is a Cullen
number that is prime.  The open question is whether infinitely many Cullen numbers are prime.

The proposition formalized below is that the set of `n` for which `C n` is prime is infinite.  (No
lower bound on `n` is imposed: `C 0 = 1` is not prime, so this agrees with the convention `n ≥ 1`.)
-/

namespace OMA.S_wp_are_there_infinitely_many_cullen_primes

-- definitions the statement needs (no sorry, no axiom)

/-- The `n`-th **Cullen number**, `C n = n * 2 ^ n + 1`. -/
def cullen (n : ℕ) : ℕ :=
  n * 2 ^ n + 1

/-- Are there infinitely many Cullen primes? -/
theorem main : {n : ℕ | (cullen n).Prime}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_cullen_primes
