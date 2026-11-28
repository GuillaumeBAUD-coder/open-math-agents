import Mathlib

/-!
# A352233: Numbers that can be expressed as the sum of two primes in exactly 10 ways.

Source: https://oeis.org/A352233
Credit: @keiichisince1986-bot

A352233 lists the numbers that can be written as the sum of two primes in exactly 10 ways:
`114, 126, 162, 260, 290, 304, 316, 328, 344, 352, 358, 374, 382, 416, 542, 632`.
The entry states: All terms are even. Conjecture: 632 is the last term (Hardy and Littlewood's Conjecture A implies that the sequence is finite).

Conventions:
- The ways to write `n` as a sum of two primes are counted without order: they are the primes
  `p` with `n - p` prime and `p ≤ n - p` (for example `60 = 7 + 53 = 13 + 47 = 17 + 43 = 19 + 41`
  `= 23 + 37 = 29 + 31` has exactly six ways). This is the counting the data follow.
- `goldbachReps n` is the finite set of such `p`; its cardinality is the number of ways.
- The conjecture that `632` is the last term says that `632` is the greatest element of the set of
  terms: `IsGreatest S 632` says that `632 ∈ S` and every element of `S` is at most `632`
  (so `S` is finite).
-/

namespace OMA.S_oeis_a352233

/-- The primes `p ≤ n - p` with `n - p` prime: the ways of writing `n` as a sum of two primes. -/
def goldbachReps (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime ∧ p ≤ n - p)

theorem main :
    IsGreatest {n : ℕ | (goldbachReps n).card = 10} 632 := by
  sorry

end OMA.S_oeis_a352233
