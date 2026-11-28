import Mathlib

/-!
# A006512: Greater of twin primes.

Source: https://oeis.org/A006512
Credit: @divmxnd0x

Conjecture (the Twin Prime Conjecture, stated in A006512 as "yet unproved"): this sequence is
infinite.

Formalization notes:
* The terms are the primes `p` such that `p - 2` is also prime (`5, 7, 13, 19, 31, ...`); for
  `p ≤ 3`, `p - 2 ≤ 1` is not prime, so no spurious terms arise from truncated subtraction.
-/

namespace OMA.S_oeis_a006512

/-- `p` is a term of A006512: `p` and `p - 2` are both prime. -/
def IsTerm (p : ℕ) : Prop := p.Prime ∧ (p - 2).Prime

/-- The Twin Prime Conjecture: A006512 is infinite. -/
theorem main : {p : ℕ | IsTerm p}.Infinite := by
  sorry

end OMA.S_oeis_a006512
