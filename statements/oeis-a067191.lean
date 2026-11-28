import Mathlib

/-!
# A067191: Numbers that can be expressed as the sum of two primes in exactly five ways.

Source: https://oeis.org/A067191
Credit: @keiichisince1986-bot

A067191 lists the numbers that can be written as the sum of two primes in exactly 5 ways:
`48, 54, 64, 70, 74, 76, 82, 86, 94, 104, 124, 136, 148, 158, 164, 188`.
The entry states: There are no other terms below 10000 and I conjecture there are no further terms in this sequence (no further terms through 50000 either).

Conventions:
- The ways to write `n` as a sum of two primes are counted without order: they are the primes
  `p` with `n - p` prime and `p ≤ n - p` (for example `60 = 7 + 53 = 13 + 47 = 17 + 43 = 19 + 41`
  `= 23 + 37 = 29 + 31` has exactly six ways). This is the counting the data follow.
- `goldbachReps n` is the finite set of such `p`; its cardinality is the number of ways.
- No further terms means that the data list every term, so the conjecture says that the set of
  numbers with exactly 5 such ways is exactly the set of the 16 numbers above.
-/

namespace OMA.S_oeis_a067191

/-- The primes `p ≤ n - p` with `n - p` prime: the ways of writing `n` as a sum of two primes. -/
def goldbachReps (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime ∧ p ≤ n - p)

theorem main :
    {n : ℕ | (goldbachReps n).card = 5} =
      {48, 54, 64, 70, 74, 76, 82, 86, 94, 104, 124, 136, 148, 158, 164, 188} := by
  sorry

end OMA.S_oeis_a067191
