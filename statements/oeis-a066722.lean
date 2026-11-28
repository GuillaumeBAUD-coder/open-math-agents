import Mathlib

/-!
# A066722: Numbers that can be expressed as the sum of two primes in exactly six ways.

Source: https://oeis.org/A066722
Credit: @keiichisince1986-bot

A066722 lists the numbers that can be written as the sum of two primes in exactly 6 ways:
`60, 66, 72, 100, 106, 110, 116, 118, 134, 146, 166, 172, 182, 212, 248, 332`.
The entry states: No other terms below 10000. I conjecture there are no further terms in this sequence.

Conventions:
- The ways to write `n` as a sum of two primes are counted without order: they are the primes
  `p` with `n - p` prime and `p ≤ n - p` (for example `60 = 7 + 53 = 13 + 47 = 17 + 43 = 19 + 41`
  `= 23 + 37 = 29 + 31` has exactly six ways). This is the counting the data follow.
- `goldbachReps n` is the finite set of such `p`; its cardinality is the number of ways.
- No further terms means that the data list every term, so the conjecture says that the set of
  numbers with exactly 6 such ways is exactly the set of the 16 numbers above.
-/

namespace OMA.S_oeis_a066722

/-- The primes `p ≤ n - p` with `n - p` prime: the ways of writing `n` as a sum of two primes. -/
def goldbachReps (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime ∧ p ≤ n - p)

theorem main :
    {n : ℕ | (goldbachReps n).card = 6} =
      {60, 66, 72, 100, 106, 110, 116, 118, 134, 146, 166, 172, 182, 212, 248, 332} := by
  sorry

end OMA.S_oeis_a066722
