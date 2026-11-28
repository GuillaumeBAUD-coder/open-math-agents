import Mathlib

/-!
# A160678: Numbers n whose abundancy is equal to 13/2; sigma(n)/n = 13/2.

Source: https://oeis.org/A160678
Credit: @keiichisince1986-bot

A160678 lists the numbers `n` with `σ(n)/n = 13/2`, where `σ(n)` is the sum of the divisors of
`n`. Its first term is `170974031122008628879954060917200710847692800`.
The entry states: This sequence includes many terms but it is conjectured to be finite.

Conventions:
- `σ(n)` is `∑ d ∈ n.divisors, d`, and the abundancy `σ(n)/n` is computed in `ℚ`. We restrict to
  positive `n`, for which the abundancy is defined.
- The conjecture says that the set of positive `n` with abundancy `13/2` is finite.
-/

namespace OMA.S_oeis_a160678

theorem main :
    {n : ℕ | 0 < n ∧ ((∑ d ∈ n.divisors, d : ℕ) : ℚ) / n = 13 / 2}.Finite := by
  sorry

end OMA.S_oeis_a160678
