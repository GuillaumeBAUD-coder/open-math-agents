import Mathlib

/-!
# Do any (2, 5)-perfect numbers exist?

Source: https://en.wikipedia.org/wiki/Superperfect_number#Generalizations
Credit: @Andyi955

Write `sigma n` for the sum of the positive divisors of `n`. A positive integer `n` is
`(m, k)`-perfect if `sigma` iterated `m` times at `n` equals `k * n`; the case `(2, 2)` gives the
superperfect numbers, and `(1, 2)` the perfect numbers (Wikipedia, Superperfect number,
section Generalizations). The question is whether any `(2, 5)`-perfect number exists, i.e. whether
some positive `n` satisfies `sigma (sigma n) = 5 * n`. None is known.

## Encoding

* `sumDivisors n` is the sum of the divisors of `n`, `∑ d ∈ n.divisors, d` with Mathlib's
  `Nat.divisors` (so `sumDivisors 0 = 0`).
* A `(2, 5)`-perfect number is a positive `n` with `sumDivisors (sumDivisors n) = 5 * n`; the
  positivity hypothesis is the source's positive integer, and it also removes the degenerate
  `n = 0`.
-/

namespace OMA.S_wp_do_any_2_5_perfect_numbers_exist

/-- `sumDivisors n` is the sum of the positive divisors of `n`. -/
def sumDivisors (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- **Do any (2, 5)-perfect numbers exist?**: some positive `n` has `sigma (sigma n) = 5 * n`. -/
theorem main : ∃ n : ℕ, 0 < n ∧ sumDivisors (sumDivisors n) = 5 * n := by
  sorry

end OMA.S_wp_do_any_2_5_perfect_numbers_exist
