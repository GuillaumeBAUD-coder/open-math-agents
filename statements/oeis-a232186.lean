import Mathlib

/-!
# A232186: Number of ways to write n = p + q (q > 0) with p and p^3 + n*q^2 both prime.

Source: https://oeis.org/A232186
Credit: @keiichisince1986-bot

A232186 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 2.

Conventions:
- `a(n) > 0` means that there is at least one such representation: a prime `p` and a positive
  integer `q` with `n = p + q` and `p^3 + n q^2` prime.
-/

namespace OMA.S_oeis_a232186

theorem main :
    ∀ n : ℕ, 2 < n → ∃ p q : ℕ, 0 < q ∧ n = p + q ∧ p.Prime ∧ (p ^ 3 + n * q ^ 2).Prime := by
  sorry

end OMA.S_oeis_a232186
