import Mathlib

/-!
# Are there any Wieferich primes in base 47?

Source: https://en.wikipedia.org/wiki/Wieferich_prime
Credit: @rabdelaal

A prime `p` is a Wieferich prime to base `a` when `a^(p-1) ≡ 1 (mod p^2)`
(the base-`2` case is the classical notion; see Wikipedia, *Wieferich prime*,
section *Generalizations*, and `WieferichPrime.IsWieferichPrimeBase` in
FormalConjectures, where the same question appears as
`exists_isWieferichPrimeBase_47`). Wikipedia's list of unsolved problems asks
whether there is any Wieferich prime to base `47`; none is currently known.
-/

namespace OMA.S_wp_are_there_any_wieferich_primes_in_base_47

/-- `p` is a Wieferich prime to base `a` when `p` is prime and
`a^(p-1) ≡ 1 (mod p^2)`. -/
def IsWieferichPrimeBase (a p : ℕ) : Prop :=
  Nat.Prime p ∧ a ^ (p - 1) % p ^ 2 = 1

/-- Are there any Wieferich primes to base `47`? -/
theorem main : ∃ p, IsWieferichPrimeBase 47 p := by
  sorry

end OMA.S_wp_are_there_any_wieferich_primes_in_base_47
