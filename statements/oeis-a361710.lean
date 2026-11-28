import Mathlib

/-!
# A361710: a(n) = Sum_{k = 0..n-1} (-1)^k * binomial(n, k) * binomial(n - 1, k)^2

Source: https://oeis.org/A361710
Credit: @ceejcake

OEIS A361710 (offset 0) is defined by
`a(n) = ∑_{k = 0}^{n - 1} (-1)^k * C(n, k) * C(n - 1, k)^2`,
with initial values `a(0)..a(7) = 0, 1, -1, -8, 15, 126, -280, -2400`.
At `n = 0`, `Finset.range 0` is empty so `a 0 = 0`, matching OEIS offset 0.
For `n ≥ 1`, `k ∈ Finset.range n` ranges over `0 ≤ k ≤ n - 1`.

Conjecture (Peter Bala, OEIS A361710):
For all primes `p ≥ 5` and positive integers `n` and `k`,
`a(n * p^k) ≡ a(n * p^(k - 1)) (mod p^(3 * k))`.
Since `0 < k`, natural-number subtraction `k - 1` is exact.
-/

namespace OMA.S_oeis_a361710

/-- The integer sequence OEIS A361710:
`a(n) = ∑_{k = 0}^{n - 1} (-1)^k * C(n, k) * C(n - 1, k)^2` for `n ≥ 0`
(with `a(0) = 0` as the empty sum). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (-1 : ℤ) ^ k * (n.choose k : ℤ) * ((n - 1).choose k : ℤ) ^ 2

/-- Supercongruence conjecture for OEIS A361710:
for all primes `p ≥ 5` and positive integers `n` and `k`,
`a(n * p^k) ≡ a(n * p^(k - 1)) (mod p^(3 * k))`. -/
theorem main :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < k →
      a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := by
  sorry

end OMA.S_oeis_a361710
