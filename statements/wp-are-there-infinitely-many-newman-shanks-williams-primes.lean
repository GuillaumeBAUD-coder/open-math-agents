import Mathlib

/-!
# Are there infinitely many Newman–Shanks–Williams primes?

Source: https://en.wikipedia.org/wiki/Newman–Shanks–Williams_prime
Credit: @gunnerhowe

The source defines the sequence `S` by `S 0 = 1`, `S 1 = 1`, `S n = 2 * S (n - 1) + S (n - 2)`
for `n ≥ 2` (OEIS A001333: 1, 1, 3, 7, 17, 41, 99, ...), and calls a prime an NSW prime when it
can be written as `S (2 * m + 1)` (closed form `((1 + √2) ^ (2m+1) + (1 - √2) ^ (2m+1)) / 2`).
The first NSW primes are 7, 41, 239, 9369319, ... (OEIS A088165), at indices 3, 5, 7, 19, ...
The open question is whether there are infinitely many; it is stated in its positive form.
Note that `S 2 = 3` is prime but sits at an even index, so by the source's definition it is not
an NSW prime.
-/

namespace OMA.S_wp_are_there_infinitely_many_newman_shanks_williams_primes

/-- The sequence `S` of the source: `S 0 = 1`, `S 1 = 1`, `S (n + 2) = 2 * S (n + 1) + S n`. -/
def S : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * S (n + 1) + S n

/-- A Newman–Shanks–Williams prime: a prime of the form `S (2 * m + 1)`. -/
def IsNSWPrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ m : ℕ, p = S (2 * m + 1)

/-- There are infinitely many Newman–Shanks–Williams primes. -/
theorem main : {p : ℕ | IsNSWPrime p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_newman_shanks_williams_primes
