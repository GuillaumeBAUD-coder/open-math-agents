import Mathlib

/-!
# Every even number greater than 4208 is the sum of two primes which both have a twin

Source: https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source, from the list of unsolved problems in mathematics: every even number greater than
`4208` is the sum of two primes which both have a twin, that is, each of the two primes differs by
`2` from another prime.

So the proposition formalized below is: every even `n > 4208` is `p + q` where each of `p` and `q`
has a twin prime partner.
-/

namespace OMA.S_wp_primes

-- definitions the statement needs (no sorry, no axiom)

/-- `p` has a **twin**: `p` is prime and `p + 2` or `p - 2` is prime. -/
def HasTwinPrimePartner (p : ℕ) : Prop :=
  p.Prime ∧ (p + 2).Prime ∨ 1 < p ∧ p.Prime ∧ (p - 2).Prime

/-- Every even number greater than 4208 is the sum of two primes which both have a twin. -/
theorem main : ∀ n : ℕ,
    4208 < n → Even n →
      ∃ p q : ℕ, HasTwinPrimePartner p ∧ HasTwinPrimePartner q ∧ p + q = n := by
  sorry

end OMA.S_wp_primes
