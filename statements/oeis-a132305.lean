import Mathlib

/-!
# OEIS A132305: supercongruence for the sum of fifth powers of trinomial coefficients

Source: https://oeis.org/A132305
Credit: @sntntHb

A132305 is the sum of fifth powers of trinomial coefficients:
`a(n) = Sum_{k=0..2n} trinomial(n,k)^5`, where `trinomial(n,k) = [x^k] (1 + x + x^2)^n`.

Peter Bala (Aug 29 2025) conjectures: the supercongruence
`a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k))` holds for all primes `p >= 5` and positive
integers `n` and `k`.

Formalized: `trinomial n k` is the coefficient of `X^k` in `(1 + X + X^2)^n` over `ℕ`, `a n` is
the sum over `k` in `0..2n` of its fifth powers, and `main` states that for every prime
`p >= 5` and all `n, k >= 1`, `a (n * p^k)` and `a (n * p^(k-1))` are congruent modulo
`p^(2*k)`.
-/

namespace OMA.S_oeis_a132305

open Polynomial

/-- The trinomial coefficient: the coefficient of `X^k` in `(1 + X + X^2)^n`. -/
noncomputable def trinomial (n k : ℕ) : ℕ := ((1 + X + X ^ 2 : ℕ[X]) ^ n).coeff k

/-- `a(n) = Sum_{k=0..2n} trinomial(n,k)^5`. -/
noncomputable def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * n + 1), trinomial n k ^ 5

theorem main :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < k →
      a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (2 * k)] := by
  sorry

end OMA.S_oeis_a132305
