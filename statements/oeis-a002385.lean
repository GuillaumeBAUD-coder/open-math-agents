import Mathlib

/-!
# A002385: palindromic primes with palindromic prime indices

Source: https://oeis.org/A002385
Credit: @jagraj28

A002385 lists the palindromic primes: primes whose decimal expansion is a palindrome. The entry
records a conjecture (Ivan N. Ianakiev, 2014): the only primes with palindromic prime indices that
are palindromic primes themselves are 3, 5 and 11.

`main` states: the set of numbers `prime(k)` such that `k` is a palindromic prime and `prime(k)`
is a palindromic prime is exactly `{3, 5, 11}` (`prime(2) = 3`, `prime(3) = 5`,
`prime(5) = 11`).

Conventions: `prime(k)` is the `k`-th prime counted from `prime(1) = 2`, as in the OEIS; in
Mathlib this is `Nat.nth Nat.Prime (k - 1)`. The entry also notes a consequence of the
conjecture; a consequence is not a separate conjecture, so it is not stated.
-/

namespace OMA.S_oeis_a002385

/-- `n` is a palindromic prime (OEIS A002385): a prime whose decimal digits read the same
backwards. -/
def IsPalPrime (n : ℕ) : Prop :=
  n.Prime ∧ (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- `prime k`: the `k`-th prime, with `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- Ianakiev's conjecture in OEIS A002385. -/
theorem main :
    {p : ℕ | ∃ k : ℕ, IsPalPrime k ∧ p = prime k ∧ IsPalPrime p} = {3, 5, 11} := by
  sorry

end OMA.S_oeis_a002385
