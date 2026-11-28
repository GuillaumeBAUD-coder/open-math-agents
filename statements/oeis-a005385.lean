import Mathlib.Data.Nat.Prime.Defs

/-!
# A005385: Safe primes in Bertrand intervals

Vladimir Shevelev's conjecture in OEIS A005385, dated July 6, 2015.
A safe prime is a prime `p` for which `(p - 1) / 2` is also prime.
Source: https://oeis.org/A005385
-/

namespace OMA.S_oeis_a005385

theorem main :
    ∀ n : ℕ, 24 ≤ n → ∃ p : ℕ, n < p ∧ p < 2 * n ∧ p.Prime ∧ ((p - 1) / 2).Prime := by
  sorry

end OMA.S_oeis_a005385
