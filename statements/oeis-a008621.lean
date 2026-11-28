import Mathlib

/-!
# A008621: Expansion of 1/((1-x)*(1-x^4)).

Source: https://oeis.org/A008621
Credit: @divmxnd0x

Conjecture (Oppermann's conjecture, stated in A008621): the terms count the odd numbers between
consecutive quarter-squares (A002620), and between consecutive quarter-squares there is always at
least one prime.

Formalization notes:
* The quarter-squares `⌊k^2/4⌋` are `0, 0, 1, 2, 4, 6, 9, 12, 16, 20, ...`, i.e. the numbers `n^2`
  and `n (n + 1)` interleaved. Oppermann's conjecture is the standard reading: for every `n > 1`
  there is a prime strictly between `n (n - 1)` and `n^2`, and a prime strictly between `n^2` and
  `n (n + 1)` (for `n ≤ 1` these intervals contain no integer).
-/

namespace OMA.S_oeis_a008621

/-- Oppermann's conjecture: for every `n > 1` there are primes in `(n(n-1), n^2)` and in
`(n^2, n(n+1))`. -/
theorem main : ∀ n : ℕ, 1 < n →
    (∃ p : ℕ, p.Prime ∧ n * (n - 1) < p ∧ p < n ^ 2) ∧
    (∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < n * (n + 1)) := by
  sorry

end OMA.S_oeis_a008621
