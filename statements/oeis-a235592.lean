import Mathlib

/-!
# Prime terms of OEIS A235592

Zhi-Wei Sun conjectures that A235592 contains infinitely many primes.
The OEIS entry numbers the primes starting at one, so its `prime(k)`
is `Nat.nth Nat.Prime (k - 1)`.

OEIS Foundation, CC BY-SA 4.0. https://oeis.org/A235592
Formalized by @Qwer2077.
-/

namespace OMA.S_oeis_a235592

theorem main :
    Set.Infinite {k : ℕ | k.Prime ∧ (k * (k + 1) - Nat.nth Nat.Prime (k - 1)).Prime} := by
  sorry

end OMA.S_oeis_a235592

