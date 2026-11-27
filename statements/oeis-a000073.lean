import Mathlib

/-!
# A000073: Tribonacci numbers

Source: https://oeis.org/A000073
Credit: @ehsanmok (agent: Claude Code, model claude-opus-5-5)

`a(n) = a(n-1) + a(n-2) + a(n-3)` for `n ≥ 3`, with `a(0) = a(1) = 0` and `a(2) = 1`.

Conjecture (Peter Bala, Dec 28 2022, OEIS A000073): the congruence
`a(n p^(k+1)) + a(n p^k) + a(n p^(k-1)) ≡ 0 (mod p^k)` holds for positive integers `k` and `n`
and for all the primes `p` listed in A106282.

## Encoding

* `a` is the Tribonacci sequence with the OEIS offset (`a 0 = 0`, `a 1 = 0`, `a 2 = 1`).
* A106282 is the set of primes `p` such that the polynomial `x^3 - x^2 - x - 1` has no zero
  modulo `p` (equivalently, being a cubic, it is irreducible over `ZMod p`). This is
  `InA106282 p`.
* Since `k ≥ 1`, the exponent `k - 1` in `ℕ` is the ordinary `k - 1`.
* The congruence `≡ 0 (mod p^k)` is divisibility `p ^ k ∣ …` in `ℕ`.
-/

namespace OMA.S_oeis_a000073

/-- The Tribonacci numbers, OEIS A000073: `0, 0, 1, 1, 2, 4, 7, 13, 24, …`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => a (n + 2) + a (n + 1) + a n

/-- OEIS A106282: primes `p` such that `x^3 - x^2 - x - 1` has no zeros modulo `p`. -/
def InA106282 (p : ℕ) : Prop :=
  p.Prime ∧ ∀ x : ZMod p, x ^ 3 - x ^ 2 - x - 1 ≠ 0

theorem main :
    ∀ p : ℕ, InA106282 p → ∀ k n : ℕ, 0 < k → 0 < n →
      p ^ k ∣ a (n * p ^ (k + 1)) + a (n * p ^ k) + a (n * p ^ (k - 1)) := by
  sorry

end OMA.S_oeis_a000073
