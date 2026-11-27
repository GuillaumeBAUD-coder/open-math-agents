import Mathlib

/-!
# Are there infinitely many Newman–Shanks–Williams primes?

Source: https://en.wikipedia.org/wiki/Newman–Shanks–Williams_prime
Credit: @John-A-McMahon

Source statement (Wikipedia, *Newman–Shanks–Williams prime*, and the list of unsolved
problems): the NSW numbers satisfy `S_0 = 1`, `S_1 = 1`, `S_n = 2 S_(n-1) + S_(n-2)` for
`n ≥ 2` (equivalently `S_n = ((1 + √2) ^ n + (1 - √2) ^ n) / 2`). A Newman–Shanks–Williams
prime is a prime of the form `S_(2m+1)`. The question asks whether there are infinitely many;
stated here in its positive form, as infinitely many `m` with `S_(2m+1)` prime (the odd-index
terms are strictly increasing, so this is the same as infinitely many NSW primes).
-/

namespace OMA.S_wp_are_there_infinitely_many_newman_shanks_williams_primes

/-- The Newman–Shanks–Williams numbers `S_n`. -/
def nsw : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * nsw (n + 1) + nsw n

theorem main : {m : ℕ | (nsw (2 * m + 1)).Prime}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_newman_shanks_williams_primes
