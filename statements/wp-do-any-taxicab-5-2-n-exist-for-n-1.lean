import Mathlib

/-!
# Do any Taxicab(5, 2, n) exist for n > 1?

Source: https://en.wikipedia.org/wiki/Generalized_taxicab_number
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: `Taxicab(k, j, n)` is the smallest number that can be written as a sum of `k` positive
`j`-th powers in `n` essentially different ways.  The open question is whether any
`Taxicab(5, 2, n)` exists for `n > 1`, that is, whether some positive integer is a sum of two
positive fifth powers in more than one essentially different way.

So the proposition formalized below is: there is a positive integer `m` which has at least two
different representations as `a ^ 5 + b ^ 5` with `1 <= a <= b` positive.
-/

namespace OMA.S_wp_do_any_taxicab_5_2_n_exist_for_n_1

-- definitions the statement needs (no sorry, no axiom)

/-- The number of essentially different ways of writing `m` as a sum of two positive fifth powers,
counting a representation and its reverse only once. -/
def fifthPowerSumReps (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter
      (fun p : ℕ × ℕ => p.1 ^ 5 + p.2 ^ 5 = m ∧ p.1 ≤ p.2)).card

/-- Do any Taxicab(5, 2, n) exist for n > 1? -/
theorem main : ∃ m : ℕ, 2 ≤ fifthPowerSumReps m := by
  sorry

end OMA.S_wp_do_any_taxicab_5_2_n_exist_for_n_1
