import Mathlib

/-!
# Are there infinitely many Wagstaff primes?

Source: https://en.wikipedia.org/wiki/Wagstaff_prime
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: a **Wagstaff prime** is a prime number of the form `(2 ^ p + 1) / 3` where `p` is an
odd prime.  It is conjectured that there are infinitely many Wagstaff primes.

`3` divides `2 ^ p + 1` exactly when `p` is odd, so for a prime `p` the condition "`p` is an odd
prime" is stated as `3 ∣ 2 ^ p + 1`; this keeps the division exact in `ℕ` and loses nothing (the
only even prime is `2`, and `2 ^ 2 + 1 = 5` is not divisible by `3`).  The quotient is then an
integer and primality of it is a condition on `ℕ`.

So the proposition formalized below is: infinitely many primes `p` have `(2 ^ p + 1) / 3` prime,
with `3 ∣ 2 ^ p + 1`.
-/

namespace OMA.S_wp_are_there_infinitely_many_wagstaff_primes

-- definitions the statement needs (no sorry, no axiom)

/-- The **Wagstaff number** of index `p`, `(2 ^ p + 1) / 3`, together with the exactness condition
`3 ∣ 2 ^ p + 1`. -/
def IsWagstaffPrime (p : ℕ) : Prop :=
  p.Prime ∧ 3 ∣ 2 ^ p + 1 ∧ ((2 ^ p + 1) / 3).Prime

/-- Are there infinitely many Wagstaff primes? -/
theorem main : {p : ℕ | IsWagstaffPrime p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_wagstaff_primes
