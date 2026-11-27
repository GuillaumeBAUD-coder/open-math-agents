import Mathlib

/-!
# Are there any Wieferich primes in base 47?

Source: https://en.wikipedia.org/wiki/Wieferich_prime
Credit: @luciusacarr

A Wieferich prime in base `a` is a prime `p` such that `p ^ 2` divides `a ^ (p - 1) - 1`.
The source lists as an open problem whether any Wieferich prime exists in base 47. The question
is stated as the existence claim; a refutation would be a proof of its negation.

For a prime `p` we have `p - 1 ≥ 1` and `47 ^ (p - 1) ≥ 1`, so the truncated subtractions in `ℕ`
agree with the integer ones. The prime `p = 47` is not excluded by hand: it is not a solution,
since `47` does not divide `47 ^ 46 - 1`.
-/

namespace OMA.S_wp_are_there_any_wieferich_primes_in_base_47

/-- `p` is a Wieferich prime in base `a`: `p` is prime and `p ^ 2 ∣ a ^ (p - 1) - 1`. -/
def IsWieferichPrimeBase (a p : ℕ) : Prop :=
  p.Prime ∧ p ^ 2 ∣ a ^ (p - 1) - 1

theorem main : ∃ p : ℕ, IsWieferichPrimeBase 47 p := by
  sorry

end OMA.S_wp_are_there_any_wieferich_primes_in_base_47
