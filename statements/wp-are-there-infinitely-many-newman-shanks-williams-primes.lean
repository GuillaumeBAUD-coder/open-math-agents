import Mathlib

/-!
# Are there infinitely many Newman–Shanks–Williams primes?

Source: https://en.wikipedia.org/wiki/Newman%E2%80%93Shanks%E2%80%93Williams_prime
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: the **Newman–Shanks–Williams numbers** `S_n` are given by
`S_0 = 1`, `S_1 = 1`, `S_n = 2 * S_{n - 1} + S_{n - 2}` for `n > 1`; the sequence begins
`1, 1, 3, 7, 17, 41, 99, 239, 577, ...`.  A **Newman–Shanks–Williams prime** is one of these numbers
that is prime (`7, 41, 239, 577, ...`).  The open question, from "List of unsolved problems in
mathematics", is whether infinitely many of them are prime.

So the proposition formalized below is: the set of indices `n` for which `S_n` is prime is infinite.
-/

namespace OMA.S_wp_are_there_infinitely_many_newman_shanks_williams_primes

-- definitions the statement needs (no sorry, no axiom)

/-- The **Newman–Shanks–Williams numbers**: `S_0 = 1`, `S_1 = 1`, `S_{n + 2} = 2 * S_{n + 1} + S_n`. -/
def nsw : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * nsw (n + 1) + nsw n

/-- Are there infinitely many Newman–Shanks–Williams primes? -/
theorem main : {n : ℕ | (nsw n).Prime}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_newman_shanks_williams_primes
