import Mathlib

/-!
# A160024: Primes whose fourth power plus the fourth powers of 11 and 3 is prime

Source: https://oeis.org/A160024
Credit: @gblacher2

The entry lists the primes `p` such that `p ^ 4 + 11 ^ 4 + 3 ^ 4` is prime, and records the
conjecture (Ulrich Krug, 2009) that the sequence is infinite.
-/

namespace OMA.S_oeis_a160024

/-- There are infinitely many primes `p` such that `p ^ 4 + 11 ^ 4 + 3 ^ 4` is prime. -/
theorem main : {p : ℕ | p.Prime ∧ (p ^ 4 + 11 ^ 4 + 3 ^ 4).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a160024
