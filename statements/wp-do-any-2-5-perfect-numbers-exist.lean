import Mathlib

/-!
# Do any (2, 5)-perfect numbers exist?

Source: https://en.wikipedia.org/wiki/Superperfect_number#Generalizations
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: writing `sigma n` for the sum of the positive divisors of `n`, a natural number `n` is
**(m, k)-perfect** when applying `sigma` exactly `m` times to `n` gives `k * n`.  The open
question, from the generalizations of superperfect numbers, is whether any **(2, 5)-perfect**
number exists, that is, whether some `n` satisfies `sigma (sigma n) = 5 * n`.

So the proposition formalized below is: there is a positive natural number `n` whose divisor sum
has divisor sum `5 * n`.
-/

namespace OMA.S_wp_do_any_2_5_perfect_numbers_exist

-- definitions the statement needs (no sorry, no axiom)

/-- `n` is a **(2, 5)-perfect** number: applying the divisor sum twice gives `5 * n`. -/
def IsTwoFivePerfect (n : ℕ) : Prop :=
  (n.divisors.sum id).divisors.sum id = 5 * n

/-- Do any (2, 5)-perfect numbers exist? -/
theorem main : ∃ n : ℕ, 0 < n ∧ IsTwoFivePerfect n := by
  sorry

end OMA.S_wp_do_any_2_5_perfect_numbers_exist
