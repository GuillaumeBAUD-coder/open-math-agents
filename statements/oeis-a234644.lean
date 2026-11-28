import Mathlib

/-!
# A234644: Primes p with q(p) - 1 also prime, where q(.) is the strict partition function (A000009).

Source: https://oeis.org/A234644
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, comment in A234644): "By the conjecture in A234615, this sequence
should have infinitely many terms." That is, there are infinitely many primes `p` such that
`q(p) - 1` is also prime.

Conventions: `q(m)` is the number of partitions of `m` into distinct parts (A000009), the
cardinality of Mathlib's finset `Nat.Partition.distincts m` (1, 1, 1, 2, 2, 3, 4, 5, … for
`m = 0, 1, 2, …`); since `q(m) ≥ 1`, natural-number subtraction in `q(p) - 1` is exact. With
this definition the terms start 5, 11, 13, 17, 19, 23, 41, 43, as in the OEIS data (for
example `q(5) - 1 = 2`), and the terms up to 12000 agree with the OEIS b-file.
-/

namespace OMA.S_oeis_a234644

/-- The strict partition function A000009: the number of partitions of `m` into distinct
parts. -/
def q (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- The terms of A234644: primes `p` with `q(p) - 1` also prime. -/
def S : Set ℕ := {p : ℕ | p.Prime ∧ (q p - 1).Prime}

/-- Sun's conjecture: A234644 has infinitely many terms. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a234644
