import Mathlib

/-!
# A261533: Primes p such that p+2 is prime with prime(p+2)-prime(p)=6

Source: https://oeis.org/A261533
Credit: @gblacher2

The entry (Zhi-Wei Sun, 2015) lists the primes `p` such that `p + 2` is prime and
`prime(p + 2) - prime(p) = 6`, and notes that the conjecture in A261528 implies that the sequence
has infinitely many terms. This file states that the sequence is infinite.

Formalization notes:
* `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`, as in the
  statement of A261528 in this repository.
* With this definition the terms below `110000` are exactly the 40 terms listed in the OEIS data
  (3, 5, 59, 2789, ..., 106187).
-/

namespace OMA.S_oeis_a261533

/-- The `m`-th prime, `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ :=
  Nat.nth Nat.Prime (m - 1)

/-- There are infinitely many primes `p` such that `p + 2` is prime and
`prime (p + 2) = prime p + 6`. -/
theorem main :
    {p : ℕ | p.Prime ∧ (p + 2).Prime ∧ prime (p + 2) = prime p + 6}.Infinite := by
  sorry

end OMA.S_oeis_a261533
