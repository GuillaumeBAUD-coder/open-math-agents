import Mathlib

/-!
# A294200: Primes p such that 2^p - 2 is a practical number

Source: https://oeis.org/A294200
Credit: @niclorusso

Conjecture (in the comments of A294200): The sequence has infinitely many terms. In other words,
there are infinitely many practical numbers of the form 2^p - 2 with p prime.

Conventions:
* A practical number is a positive integer n such that every m with m <= n is a sum of distinct
  divisors of n (1, 2, 4, 6, 8, 12, ...).
* 2^p >= 4 for p prime, so 2^p - 2 is an exact natural-number subtraction.
-/

namespace OMA.S_oeis_a294200

/-- `n` is a practical number: every `m <= n` is a sum of distinct divisors of `n`. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m ≤ n → ∃ s ⊆ n.divisors, ∑ i ∈ s, i = m

/-- The conjecture on A294200: there are infinitely many primes `p` with `2^p - 2` practical. -/
theorem main : {p : ℕ | p.Prime ∧ IsPractical (2 ^ p - 2)}.Infinite := by
  sorry

end OMA.S_oeis_a294200
