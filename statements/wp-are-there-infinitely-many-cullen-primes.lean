import Mathlib

/-!
# Are there infinitely many Cullen primes?

Source: https://en.wikipedia.org/wiki/Cullen_number
Credit: @John-A-McMahon

Source statement (Wikipedia, *Cullen number*): a Cullen number is `C_n = n * 2 ^ n + 1` for a
natural number `n`; a Cullen prime is a Cullen number that is prime. It is conjectured that
there are infinitely many Cullen primes (only sixteen are known). Stated here in its positive
form, as infinitely many indices `n` with `C_n` prime. Whether `n = 0` is allowed does not
matter: `C_0 = 1` is not prime. Distinct `n` give distinct `C_n`, so infinitely many indices is
the same as infinitely many Cullen primes.
-/

namespace OMA.S_wp_are_there_infinitely_many_cullen_primes

/-- The Cullen number `C_n = n * 2 ^ n + 1`. -/
def cullen (n : ℕ) : ℕ := n * 2 ^ n + 1

theorem main : {n : ℕ | (cullen n).Prime}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_cullen_primes
