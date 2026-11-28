import Mathlib

/-!
# A397526: Number of ways to write 6*n as p + q, where p and q are primes such that 2*p+1 and 4*q+1 are also prime.

Source: https://oeis.org/A397526
Credit: @keiichisince1986-bot

A397526 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 0.

Conventions:
- `a(n) > 0` means that there are primes `p, q` with `6n = p + q` such that `2p + 1` and
  `4q + 1` are prime.
-/

namespace OMA.S_oeis_a397526

theorem main :
    ∀ n : ℕ, 0 < n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 6 * n = p + q ∧ (2 * p + 1).Prime ∧
        (4 * q + 1).Prime := by
  sorry

end OMA.S_oeis_a397526
