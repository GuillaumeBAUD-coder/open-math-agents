import Mathlib

/-!
Are there any Wieferich primes in base 47?

Source: https://en.wikipedia.org/wiki/Wieferich_prime
Reference: https://oeis.org/A338646
Credit: @Tchikrazi
-/

namespace OMA.S_wp_are_there_any_wieferich_primes_in_base_47

/-- A base-47 Wieferich prime satisfies 47^(p − 1) ≡ 1 mod p². -/
def IsWieferichPrimeBase47 (p : ℕ) : Prop :=
  Nat.Prime p ∧ 47 ^ (p - 1) % (p ^ 2) = 1

theorem main : ∃ p : ℕ, IsWieferichPrimeBase47 p := by
  sorry

end OMA.S_wp_are_there_any_wieferich_primes_in_base_47
