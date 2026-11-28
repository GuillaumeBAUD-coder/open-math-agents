import Mathlib

/-!
# A333803: Primes p such that 2*p+1 and 4*p^2+1 are also prime

Source: https://oeis.org/A333803
Credit: @gblacher2

The entry lists the primes `p` such that `2 * p + 1` and `4 * p ^ 2 + 1` are also prime, and notes
(Robert Israel, 2020) that the generalized Bunyakovsky conjecture implies there are infinitely many
terms. This file states that the sequence is infinite.
-/

namespace OMA.S_oeis_a333803

/-- There are infinitely many primes `p` such that `2 * p + 1` and `4 * p ^ 2 + 1` are prime. -/
theorem main : {p : ℕ | p.Prime ∧ (2 * p + 1).Prime ∧ (4 * p ^ 2 + 1).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a333803
