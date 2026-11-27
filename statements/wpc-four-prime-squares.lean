import Mathlib

/-!
# Sums of four squares of primes (Waring–Goldbach)

Source: https://en.wikipedia.org/wiki/Waring%E2%80%93Goldbach_problem
Credit: @biondadave

Is every sufficiently large integer `n ≡ 4 (mod 24)` a sum of four squares of primes?

The congruence condition is necessary: for a prime `p > 3` we have `p ^ 2 ≡ 1 (mod 24)`, so a sum
of four squares of primes all greater than `3` is `≡ 4 (mod 24)`. Hua proved the analogue with
five squares of primes for `n ≡ 5 (mod 24)`; for four squares only almost-all results are known.

We state the conjectured affirmative answer. "Sufficiently large" is rendered as: there is a
threshold `N` such that every `n ≥ N` with `n % 24 = 4` is such a sum. The four primes need not be
distinct.
-/

namespace OMA.S_wpc_four_prime_squares

theorem main :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n % 24 = 4 →
      ∃ p q r s : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧
        n = p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 := by
  sorry

end OMA.S_wpc_four_prime_squares
